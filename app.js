/* Workspace site: the agreed mock, reading live rows from Supabase.
   Every status is derived by the server (v_sessions, v_tasks); this page maps rows onto the mock's pieces, writes
   Luke's answers, messages and archive actions, and refetches on Realtime changes plus a 30 s clock, because Silent
   and Lost change with time alone. */
const CFG=window.WS_CONFIG;
const LOCAL=CFG.env==='local';
const sb=window.supabase.createClient(CFG.url,CFG.key,{auth:{flowType:'pkce',persistSession:true,autoRefreshToken:true,detectSessionInUrl:true}});
const STATS={loads:0,realtime:0,timer:0,rt:'closed',seen:[]};   // read by the browser tests: seen = recent Realtime rows
window.__wsStats=STATS;

/* ---------- live data (refilled on every load) ---------- */
let PROJECTS=[],TASKS=[],SESSIONS=[],ASKS=[],EVENTS=[],CHECKS=[];   // CHECKS: one reconciliation row per machine
let PIDX=new Map(),TIDX=new Map(),SIDX=new Map();
const CONVO={};            // session id -> {turns, msgs, gen}
const TURN_LIMIT=200,MSG_LIMIT=100;
let NOW=Date.now(),GEN=0,USER=null,READY=false,OFFLINE=false,GATE=null;

const HOST_INFO={mac:{name:'MacBook',sub:'This laptop'},jupiter:{name:'Jupiter',sub:'JSC · GH200'},horizon:{name:'Horizon',sub:'TACC · GB200'}};
const HOST_PREF=['horizon','jupiter','mac'];
function hostInfo(h){return HOST_INFO[h]||{name:h?h[0].toUpperCase()+h.slice(1):'Unknown',sub:''}}
function hostOrder(){
  const rank=h=>{const i=HOST_PREF.indexOf(h);return i<0?99:i};
  return [...new Set([...SESSIONS.map(s=>s.host),...CHECKS.map(c=>c.host)])].sort((a,b)=>rank(a)-rank(b)||a.localeCompare(b));
}

/* ---------- helpers ---------- */
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const P=id=>PIDX.get(id), T=id=>TIDX.get(id), S=k=>SIDX.get(k);
const hn=s=>hostInfo(s.host).name;
const DOW=['Sun','Mon','Tue','Wed','Thu','Fri','Sat'], MON=['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
const PTF=new Intl.DateTimeFormat('en-US',{timeZone:'America/Los_Angeles',year:'numeric',month:'numeric',day:'numeric',weekday:'short',hour:'2-digit',minute:'2-digit',hourCycle:'h23'});
function ptp(d){const o={};for(const x of PTF.formatToParts(d))o[x.type]=x.value;return {y:+o.year,m:+o.month-1,d:+o.day,wd:DOW.indexOf(o.weekday),hm:(o.hour==='24'?'00':o.hour)+':'+o.minute}}
const tms=ts=>Date.parse(String(ts).replace(/(\.\d{3})\d+/,'$1'));
const agoOf=ts=>ts?Math.max(0,Math.round((NOW-tms(ts))/60000)):null;   // minutes ago, never negative
const relOf=ts=>ts?Math.round((NOW-tms(ts))/60000):undefined;          // minutes ago, negative = future
const at=ago=>new Date(NOW-ago*60000);
const clock=ago=>ptp(at(ago)).hm;
const dayKey=ago=>{const p=ptp(at(ago));return p.y*10000+p.m*100+p.d};
function dayLabel(ago){const p=ptp(at(ago)),k=dayKey(ago);if(k===dayKey(0))return 'Today';if(k===dayKey(1440))return 'Yesterday';if(k===dayKey(-1440))return 'Tomorrow';return `${DOW[p.wd]} ${MON[p.m]} ${p.d}`}
function etaShort(a){const p=ptp(at(a));if(dayKey(a)===dayKey(0))return p.hm;if(-a<6*1440)return `${DOW[p.wd]} ${p.hm}`;return `${MON[p.m]} ${p.d}`}
function when(ago){const l=dayLabel(ago);return (l==='Today'?'':l+' ')+clock(ago)+' PT'}
function shortDay(ago){const p=ptp(at(ago));return dayKey(ago)===dayKey(0)?'Today '+p.hm:`${MON[p.m]} ${p.d}`}
function stamp(ago){return dayKey(ago)===dayKey(0)?clock(ago):shortDay(ago)+' '+clock(ago)}
function dur(m){if(m<1)return 'under a minute';if(m<60)return m+'m';if(m<1440){const h=Math.floor(m/60),r=m%60;return h<6&&r?`${h}h ${r}m`:`${h}h`}return Math.floor(m/1440)+'d'}
const ago=m=>m<1?'just now':dur(m)+' ago';
const SLABEL={working:'Working',needs:'Needs you',idle:'Idle',silent:'Silent',lost:'Lost',dead:'Dead',ended:'Ended'};
const CHIPL={needs:'waiting on you',working:'working',idle:'idle',silent:'silent',lost:'lost',dead:'dead',ended:'ended'};
const SORD={needs:0,dead:1,lost:2,silent:3,working:4,idle:5,ended:6};
const SCHIPS=['needs','working','idle','silent','lost','dead','ended'];
const TMAP={waiting:['needs','Needs you'],risk:['silent','At risk'],blocked:['dead','Blocked'],on:['working','On track'],paused:['idle','Paused'],done:['ended','Done']};
const TORD={waiting:0,risk:1,blocked:2,on:3,paused:4,done:5};
const KIND={good:'Good',bad:'Bad',resolved:'Resolved',progress:'Progress',ask:'Asked you',decision:'You decided'};
const AKIND={go:'Go-ahead',decision:'Decision',review:'Review',unblock:'Unblock'};
const isLive=s=>!['dead','ended'].includes(s.status);
function vis(t){return !!t&&!t.archived&&!!P(t.project)&&!P(t.project).archived}
const visTask=id=>!id||vis(T(id));                  // asks and news from a session with no task stay visible
const inProject=(pf,id)=>!pf||(!!T(id)&&T(id).project===pf);
const ST=s=>s.task?T(s.task):null;
function tLabel(s){const t=ST(s);return t?esc(t.name)+(vis(t)?'':' (archived)'):'No task'}
const openAsks=task=>ASKS.filter(a=>!a.answer&&(!task||a.task===task)&&visTask(a.task));
const tStatus=t=>t.health||'on';
function pHealth(p){
  const st=TASKS.filter(t=>t.project===p.id&&!t.archived).map(tStatus);
  if(st.includes('waiting'))return 'needs';
  if(st.includes('blocked')&&!st.includes('on'))return 'dead';
  if(st.includes('risk'))return 'silent';
  if(st.every(x=>x==='done'||x==='paused'))return 'ended';
  return 'working';
}
function etaState(t){
  const st=tStatus(t),e=t.eta||{},n=e.next,d=e.done;
  if(st==='done')return {c:'e-mute',v:'Done'};
  if(st==='paused')return {c:'e-mute',v:'Paused'};
  if(n&&n.at>0)return {c:'e-bad',v:'Overdue '+dur(n.at)};
  if((n&&n.mode==='you')||(d&&d.mode==='you'))return {c:'e-ask',v:'After you'};
  const x=d&&d.at!==undefined?d:n&&n.at!==undefined?n:null;
  if(x)return {c:x.kind==='measured'?'':'e-guess',v:(x.kind==='measured'?'':'~')+etaShort(x.at)};
  if(d&&d.mode==='external')return {c:'e-mute',v:'Others'};
  if(d&&d.mode==='ongoing')return {c:'e-mute',v:'Ongoing'};
  return {c:'e-mute',v:'Unknown'};
}
function etaBlock(t){
  const e=t.eta||{};if(!e.next&&!e.done)return '';
  const card=(label,x)=>{
    if(!x)return '';
    let v,rel='';
    if(x.mode==='you')v=x.after?`About ${dur(x.after)} after your answer`:'When you answer';
    else if(x.mode==='external')v='Depends on others';
    else if(x.mode==='ongoing')v='Ongoing';
    else if(x.mode==='unknown'||x.at===undefined)v='Not set yet';
    else if(x.at>0){v='Was '+when(x.at);rel=`<span class="eta-rel bad">overdue ${dur(x.at)}</span>`}
    else{v=when(x.at);rel=`<span class="eta-rel">in ${dur(-x.at)}</span>`}
    const tag=x.kind==='measured'?'<span class="basis m">Measured</span>':x.kind==='estimate'?'<span class="basis">Estimate</span>':'';
    return `<div class="eta-card"><span class="eta-l">${label}</span>${x.what?`<b>${esc(x.what)}</b>`:''}<span class="eta-v">${v}${rel}</span><span class="eta-b">${tag}${esc(x.basis||'')}</span></div>`;
  };
  return `<section class="dr-sec"><h4>ETA</h4><div class="eta-grid">${card('Next milestone',e.next)}${card('Whole task',e.done)}</div>
    ${e.hist?`<div class="slips"><div class="slips-h">How the whole-task ETA moved</div>${e.hist.map(([set,to,why])=>`<div class="slip"><span class="mono">set ${esc(set)}</span><b>${esc(to)}</b><span>${esc(why)}</span></div>`).join('')}</div>`:''}</section>`;
}
const spill=s=>`<span class="pill" data-s="${s}">${SLABEL[s]||esc(s)}</span>`;
function tpill(st,t){const [k,l]=TMAP[st]||TMAP.on;return `<span class="pill" data-s="${k}">${l}${t&&t.verdict&&st==='done'?' · '+esc(t.verdict):''}</span>`}
const strip=s=>`<div class="strip" aria-label="Last 24 hours">${s.cells.map(c=>`<i data-c="${c}"></i>`).join('')}</div>`;
const safeUrl=u=>typeof u==='string'&&/^https?:\/\//i.test(u)?u:null;
const hostOf=u=>{try{return new URL(u).host.replace(/^www\./,'')}catch(e){return 'the web'}};
function linkLabel(u){try{const x=new URL(u);let p=x.pathname.replace(/\/$/,'');if(p.length>42)p='…'+p.slice(-40);return x.host.replace(/^www\./,'')+p}catch(e){return u}}
function normLinks(l){
  if(!l)return [];
  return (Array.isArray(l)?l:[l]).map(x=>{const h=typeof x==='string'?x:x&&(x.href||x.url);return safeUrl(h)?{href:h,label:(x&&x.label)||linkLabel(h)}:null}).filter(Boolean);
}
const links=ls=>ls&&ls.length?` · <span class="lnks">${ls.map(l=>`<a href="${esc(l.href)}" target="_blank" rel="noopener">${esc(l.label)} ↗</a>`).join('')}</span>`:'';
function prettyModel(m){
  if(!m)return '';
  const x=/^claude-([a-z]+)-(\d+)(?:-(\d+))?/.exec(m);
  return x?x[1][0].toUpperCase()+x[1].slice(1)+' '+x[2]+(x[3]&&x[3].length<3?'.'+x[3]:''):m;
}
function heardText(s){
  if(s.status==='ended')return 'ended '+ago(s.ended??s.heard);
  if(s.status==='dead')return 'died '+ago(s.gone??s.heard);
  if(s.status==='silent'&&s.due!=null)return 'due back '+ago(Math.max(0,s.due));
  return 'heard '+ago(s.heard);
}
function statusNote(s){
  if(s.status==='silent')return `It was due back by ${s.due!=null?clock(s.due)+' PT':'now'} and has not reported since. Its process is still alive, so it may be stuck rather than dead.`;
  if(s.status==='lost')return `Nothing has been heard from it, hook or sidecar, since ${when(s.heard)}. It may still be running, or its machine may have dropped it.`;
  if(s.status==='dead')return `Its process disappeared at ${when(s.gone??s.heard)} without a clean end, so anything it was watching may have finished with nobody looking.`;
  if(s.status==='ended')return `Ended ${when(s.ended??s.heard)}${s.endReason?` (${s.endReason})`:''}${s.handoff?', with a handoff':''}.`;
  return s.activity||'No activity reported yet.';
}

/* ---------- rows to the mock's shapes ---------- */
function mapEta(x){
  if(!x)return null;
  const o={what:x.what||'',kind:x.kind||null,basis:x.basis||'',mode:x.mode||null};
  if(x.at)o.at=relOf(x.at);
  if(x.after_min!=null)o.after=+x.after_min;
  return o;
}
function etaTo(x){
  if(!x)return 'Cleared';
  if(x.at){const p=ptp(new Date(tms(x.at)));return `${DOW[p.wd]} ${MON[p.m]} ${p.d}`}
  return {you:'After you',external:'Depends on others',ongoing:'Ongoing'}[x.mode]||'Not set';
}
function mapTask(r){
  const hist=(r.eta_history||[]).filter(c=>c.which==='done').map(c=>[shortDay(agoOf(c.set_at)),etaTo(c.new),c.why||(c.old?'':'First plan')]);
  return {id:r.id,project:r.project_id,name:r.name,base:r.set_status,health:r.health,verdict:r.verdict,archived:!!r.archived_at,
    goal:r.goal,next:r.next,overdue:r.eta_overdue,
    steps:(r.milestones||[]).map(m=>[m.name,m.state,m.note||(['done','failed'].includes(m.state)&&m.changed_at?shortDay(agoOf(m.changed_at)):'')]),
    eta:{next:mapEta(r.eta_next),done:mapEta(r.eta_done),hist:hist.length>1?hist:null},
    last:r.last_event?{h:r.last_event.headline,ago:agoOf(r.last_event.ts)}:null};
}
function mapSession(r){
  return {key:r.id,id:r.id,name:r.name||r.task_name||'Session '+r.id.slice(0,8),task:r.task_id,
    agent:r.agent==='codex'?'Codex':'Claude',model:prettyModel(r.model),host:r.host,machine:r.machine||r.host,
    path:r.cwd||'',tmux:r.tmux_session||null,pane:r.tmux_pane||null,branch:r.branch||'',rc:r.rc_id||null,status:r.status,
    heard:agoOf(r.last_seen_at),started:agoOf(r.started_at),ended:agoOf(r.ended_at),gone:agoOf(r.pid_gone_at),
    due:r.expect_next_by?relOf(r.expect_next_by):null,activity:r.activity||'',handoff:r.handoff||null,endReason:r.end_reason||'',
    cells:(r.strip||'').padStart(48,'-').slice(-48).split(''),lastTurn:r.last_turn};
}
const mapAsk=r=>({id:r.id,task:r.task_id,s:r.session_id,kind:AKIND[r.kind]||r.kind,ago:agoOf(r.ts),blocking:r.blocking,
  q:r.question,ctx:r.context||'',cost:r.cost||'',options:r.options||[],link:safeUrl(r.link)?{label:'Open the link on '+hostOf(r.link),href:r.link}:null,
  answer:r.answer!=null?{choice:r.answer,ago:agoOf(r.answered_at)}:null});
const mapEvent=r=>({id:r.id,ago:agoOf(r.ts),kind:r.kind,task:r.task_id,s:r.session_id,h:r.headline,sys:r.auto,detail:r.detail||'',links:normLinks(r.links)});

/* ---------- resume ---------- */
function resume(s){
  const live=!['dead','ended'].includes(s.status);
  if(s.agent==='Codex')return live&&s.tmux?`ssh ${s.host} -t 'tmux attach -t ${s.tmux}'`:`ssh ${s.host} -t 'cd ${s.path} && codex resume ${s.id}'`;
  if(s.host==='mac')return `cd ${s.path} && claude --resume ${s.id}`;
  if(live&&s.tmux)return `ssh ${s.host} -t 'tmux attach -t ${s.tmux}'`;
  return `ssh ${s.host} -t 'tmux new -s ${s.tmux||'resume'} "cd ${s.path} && claude --resume ${s.id}"'`;
}
const fresh=s=>resume({...s,status:'dead'});   // the command for when the pane is gone
function resumeHint(s){
  const live=!['dead','ended'].includes(s.status);
  if(s.host==='mac')return live?'It is open in a Terminal tab now. This reopens the same conversation if you closed that tab.':'Reopens the same conversation in its folder.';
  if(s.status==='lost'&&s.tmux)return `Nothing has been heard from it for ${dur(s.heard)}, so its pane on ${hn(s)} may be gone. If attaching fails, the second command opens a fresh pane and reopens the same conversation.`;
  if(live&&s.tmux)return `Attaches to its tmux pane on ${hn(s)}, so you land in the live session.`;
  return `Its pane is gone, so this opens a fresh tmux pane on ${hn(s)} and reopens the same conversation there.`;
}

const sv=(d,w=16)=>`<svg width="${w}" height="${w}" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${d}</svg>`;
const ICON={
  today:sv('<rect x="2" y="2" width="5" height="5" rx="1.2"/><rect x="9" y="2" width="5" height="5" rx="1.2"/><rect x="2" y="9" width="5" height="5" rx="1.2"/><rect x="9" y="9" width="5" height="5" rx="1.2"/>'),
  asks:sv('<path d="M3.5 14V2.5h8.5l-1.6 3 1.6 3H3.5"/>'),
  sessions:sv('<rect x="1.5" y="2.5" width="13" height="11" rx="2"/><path d="M4.5 6.5l2 1.5-2 1.5M8 10h3.5"/>'),
  news:sv('<path d="M3 4h10M3 8h10M3 12h6"/>'),
  api:sv('<path d="M5.5 2.5C4 2.5 4.2 4 4.2 5.5S3.5 8 2.5 8c1 0 1.7.8 1.7 2.5S4 13.5 5.5 13.5M10.5 2.5c1.5 0 1.3 1.5 1.3 3S12.5 8 13.5 8c-1 0-1.7.8-1.7 2.5s.2 3-1.3 3"/>'),
  copy:sv('<rect x="5.5" y="5.5" width="8" height="8" rx="1.5"/><path d="M10.5 5.5v-2a1 1 0 0 0-1-1h-6a1 1 0 0 0-1 1v6a1 1 0 0 0 1 1h2"/>',14),
  term:sv('<path d="M3 4.5l3 3.5-3 3.5M8 12h5"/>',14),
  ext:sv('<path d="M9 2.5h4.5V7M13.5 2.5L7 9M11.5 9.5v3a1 1 0 0 1-1 1h-7a1 1 0 0 1-1-1v-7a1 1 0 0 1 1-1h3"/>',13),
  x:sv('<path d="M4 4l8 8M12 4l-8 8"/>'),
  check:sv('<path d="M4 8.5l2.5 2.5L12 5.5"/>',12),
  cross:sv('<path d="M5 5l6 6M11 5l-6 6"/>',12),
  chat:sv('<path d="M2.5 3h11v7.5H8L4.5 13v-2.5h-2z"/>'),
  talk:sv('<path d="M2.5 3h11v7.5H8L4.5 13v-2.5h-2z"/>',14),
  archive:sv('<rect x="1.5" y="2.5" width="13" height="3.5" rx="1"/><path d="M2.75 6v6.5a1 1 0 0 0 1 1h8.5a1 1 0 0 0 1-1V6M6.5 9h3"/>',14)
};
const MARK='<span class="brand-mark"><svg width="16" height="16" viewBox="0 0 16 16" fill="currentColor" aria-hidden="true"><rect x="1" y="2" width="14" height="3" rx="1.2"/><rect x="3.5" y="6.5" width="11.5" height="3" rx="1.2"/><rect x="6" y="11" width="9" height="3" rx="1.2"/></svg></span>';

/* ---------- state ---------- */
const state={view:'today',project:null,sf:'all',q:'',nf:'all',drawer:null,confirm:null,chat:null};

/* ---------- pieces ---------- */
function askCard(a,ctx){
  const s=S(a.s),t=a.task&&T(a.task),rid=`reply-${a.id}-${ctx}`;
  return `<article class="ask" data-ask="${a.id}">
    <header class="ask-h"><span class="kind" data-k="ask">${esc(a.kind)}</span><span class="ask-age">waiting <b>${dur(a.ago)}</b></span></header>
    <h3 class="ask-q">${esc(a.q)}</h3>
    ${a.ctx?`<p class="ask-ctx">${esc(a.ctx)}</p>`:''}
    ${a.cost?`<div class="ask-cost"><span>Cost</span>${esc(a.cost)}</div>`:''}
    ${a.link?`<a class="more" href="${esc(a.link.href)}" title="${esc(a.link.href)}" target="_blank" rel="noopener">${esc(a.link.label)} ↗</a>`:''}
    <div class="ask-from">From ${s?`<button data-act="session" data-id="${s.key}">${hn(s)} · ${esc(s.name)}</button>`:'a removed session'}${t?` on <button data-act="task" data-id="${t.id}">${esc(t.name)}</button>`:''}${a.blocking?'<span class="hold">holding its turn</span>':''}</div>
    <div class="ask-opts">${a.options.map((o,i)=>`<button class="btn ${i===0?'primary':''}" data-act="answer" data-id="${a.id}" data-opt="${esc(o)}">${esc(o)}</button>`).join('')}<button class="btn ghost" data-act="reply" data-id="${a.id}">Write a reply</button></div>
    <div class="ask-reply" hidden><label for="${rid}" class="ask-age">Your reply goes back to the session as its answer</label><textarea id="${rid}" rows="2" placeholder="e.g. Go, but cap it at 16 node-h"></textarea><button class="btn primary sm" data-act="send" data-id="${a.id}">Send</button></div>
  </article>`;
}
function segs(t){return `<div class="segs">${t.steps.map(x=>`<i data-m="${x[1]}"></i>`).join('')}</div>`}
function taskRow(t){
  const st=tStatus(t),ev=t.last,ss=SESSIONS.filter(s=>s.task===t.id),done=t.steps.filter(x=>x[1]==='done').length,eta=etaState(t);
  return `<div class="trow ${st==='done'||st==='paused'?'quiet':''}" data-act="task" data-id="${t.id}" role="button" tabindex="0">
    <div class="t-st">${tpill(st,t)}</div>
    <div class="t-main"><div class="t-name">${esc(t.name)}</div><div class="t-last">${ev?esc(ev.h):esc(t.next)}</div></div>
    <div class="t-eta ${eta.c}" title="ETA. ~ means estimated, plain means measured from a rate"><small>ETA</small><b>${esc(eta.v)}</b></div>
    <div class="t-prog" title="${done} of ${t.steps.length} milestones">${segs(t)}<span>${t.steps.length?`${done}/${t.steps.length}`:'No plan'}</span></div>
    <div class="t-sess">${ss.map(s=>`<span class="sdot" data-s="${s.status}" title="${hn(s)} · ${esc(s.name)}: ${SLABEL[s.status]}"></span>`).join('')}</div>
    <div class="t-age">${ev?ago(ev.ago):''}</div>
  </div>`;
}
function projectBlock(p){
  const ts=TASKS.filter(t=>t.project===p.id&&!t.archived).sort((a,b)=>TORD[tStatus(a)]-TORD[tStatus(b)]);
  const st=ts.map(tStatus),n=k=>st.filter(x=>x===k).length;
  const tags=[n('waiting')&&`<span class="pill" data-s="needs">${n('waiting')} needs you</span>`,n('risk')&&`<span class="pill" data-s="silent">${n('risk')} at risk</span>`,n('blocked')&&`<span class="pill" data-s="dead">${n('blocked')} blocked</span>`].filter(Boolean).join('');
  const fallback=st.every(x=>x==='done'||x==='paused')?'<span class="pill" data-s="ended">Quiet</span>':'<span class="pill" data-s="working">On track</span>';
  const c=state.confirm;
  return `<article class="proj" data-project="${p.id}"><header class="proj-h"><div><h3>${esc(p.name)}</h3>${p.blurb?`<p>${esc(p.blurb)}</p>`:''}</div><div class="proj-tags">${tags||fallback}<button class="btn sm ghost icon" data-act="confirm" data-kind="archive-project" data-id="${p.id}" title="Archive project" aria-label="Archive ${esc(p.name)}">${ICON.archive}</button></div></header>${c&&c.kind==='archive-project'&&c.id===p.id?confirmBar('archive-project',p.id):''}${ts.map(taskRow).join('')}</article>`;
}
function newsItem(e){
  const t=e.task&&T(e.task),s=e.s&&S(e.s);
  const act=t?`data-act="task" data-id="${t.id}" role="button" tabindex="0"`:s?`data-act="session" data-id="${s.key}" role="button" tabindex="0"`:'';
  return `<div class="ni" ${act} data-event="${e.id}">
    <span class="kind" data-k="${e.kind}">${KIND[e.kind]||esc(e.kind)}${e.sys?'<em>auto</em>':''}</span>
    <div><div class="ni-h">${esc(e.h)}</div>${e.detail?`<div class="ni-d">${esc(e.detail)}</div>`:''}<div class="ni-m">${[t?esc(t.name):'',s?`${hn(s)} · ${esc(s.name)}`:'',when(e.ago)].filter(Boolean).join(' · ')}${links(e.links)}</div></div>
  </div>`;
}
function sessionRow(s){
  return `<div class="srow ${s.status==='ended'?'quiet':''}" data-act="session" data-id="${s.key}" role="button" tabindex="0">
    <div class="s-st">${spill(s.status)}<span class="heard">${heardText(s)}</span></div>
    <div class="s-main"><div class="s-name">${esc(s.name)}<span class="agent">${s.agent}</span></div><div class="s-act">${tLabel(s)}${s.activity?' · '+esc(s.activity):''}</div></div>
    <div class="s-where"><span class="mono path" title="${esc(s.path)}">&lrm;${esc(s.path)}&lrm;</span>${s.tmux?`<span class="mono tm">tmux ${esc(s.tmux)} · ${esc(s.machine)}</span>`:`<span class="mono tm">Terminal tab · ${esc(s.machine)}</span>`}</div>
    <div class="s-strip">${strip(s)}</div>
    <div class="s-btns"><button class="btn sm" data-act="chat" data-id="${s.key}" aria-label="Talk">${ICON.talk}<span class="bl">Talk</span></button><button class="btn sm" data-act="copy" data-text="${esc(resume(s))}" data-label="resume command" aria-label="Copy resume command">${ICON.term}<span class="bl">Resume</span></button><button class="btn sm ghost icon" data-act="copy" data-text="${esc(s.id)}" data-label="session id" title="Copy session id" aria-label="Copy session id">${ICON.copy}</button></div>
  </div>`;
}
function statusChips(act,current){
  return SCHIPS.map(k=>{
    const n=SESSIONS.filter(s=>s.status===k).length;
    return n?`<button class="chip" data-act="${act}" data-id="${k}" ${current===k?'aria-pressed="true"':''}><span class="sdot" data-s="${k}"></span>${n} ${CHIPL[k]}</button>`:'';
  }).join('');
}
const LEGEND='<span><i style="background:var(--ok)"></i>working</span><span><i style="background:var(--ask-dot)"></i>waiting on you</span><span><i style="background:color-mix(in srgb,var(--idle) 45%,transparent)"></i>idle</span><span><i style="background:var(--warn)"></i>silent</span><span><i style="background:var(--off)"></i>no heartbeat, lost, dead or ended</span>';

/* ---------- views ---------- */
function lede(pf){
  const a=openAsks().filter(x=>!pf||inProject(pf,x.task));
  const ss=SESSIONS.filter(s=>!pf||(ST(s)&&ST(s).project===pf));
  const w=ss.filter(s=>s.status==='working').length;
  const bad=ss.filter(s=>['silent','lost','dead'].includes(s.status)&&(!ST(s)||vis(ST(s))));
  let t=a.length?`<b>${a.length} ${a.length>1?'asks wait':'ask waits'} on you</b>, the oldest for ${dur(Math.max(...a.map(x=>x.ago)))}. `:'Nothing waits on you. ';
  t+=`${w} ${w===1?'session is':'sessions are'} working. `;
  const what=s=>s.status==='silent'?'went silent '+ago(Math.max(0,s.due??0)):s.status==='lost'?'lost contact '+ago(s.heard):'died '+ago(s.gone??s.heard);
  const said=bad.map(s=>`<button class="inline" data-act="session" data-id="${s.key}">${hn(s)} · ${esc(s.name)}</button> ${what(s)}`);
  if(said.length)t+=(said.length>1?said.slice(0,-1).join(', ')+(said.length>2?',':'')+' and '+said[said.length-1]:said[0])+'. ';
  const od=TASKS.filter(x=>vis(x)&&(!pf||x.project===pf)&&etaState(x).c==='e-bad');
  if(od.length)t+=`${od.length} ${od.length>1?'tasks are':'task is'} past ${od.length>1?'their ETAs':'its ETA'}. `;
  if(!pf)t+=unreportedSentence();
  return t;
}
// "3 Claude sessions on the MacBook are running but not reporting." from every machine's latest check
function unreportedSentence(){
  const groups=new Map();
  for(const c of CHECKS)for(const u of c.unreported){const k=c.host+'|'+AGENT_NAME(u.agent);groups.set(k,(groups.get(k)||0)+1)}
  if(!groups.size)return '';
  const parts=[...groups].map(([k,n])=>{const [h,a]=k.split('|'),name=hostInfo(h).name;
    return `<button class="inline" data-act="nav" data-id="sessions">${n} ${a} session${n>1?'s':''} on ${h==='mac'?'the ':''}${esc(name)}</button>`});
  const total=[...groups.values()].reduce((x,y)=>x+y,0);
  const list=parts.length>1?parts.slice(0,-1).join(', ')+' and '+parts[parts.length-1]:parts[0];
  return `<span data-unreported>${list} ${total>1?'are':'is'} running but not reporting.</span>`;
}
function todayLabel(){const p=ptp(new Date(NOW));return `${DOW[p.wd]} ${MON[p.m]} ${p.d} · ${p.hm} PT`}
function viewToday(){
  const pp=state.project&&P(state.project);if(!pp||pp.archived)state.project=null;
  const pf=state.project;
  const asks=openAsks().filter(a=>!pf||inProject(pf,a.task)).sort((a,b)=>(b.blocking-a.blocking)||(b.ago-a.ago));
  const projs=PROJECTS.filter(p=>!p.archived&&(!pf||p.id===pf));
  const news=EVENTS.filter(e=>visTask(e.task)&&(!pf||inProject(pf,e.task))).slice(0,pf?12:9);
  return `
  <header class="page-h">
    <div><h1>${pf?esc(P(pf).name):'Today'}</h1><p class="sub">${todayLabel()}${pf?` <button class="chip clear" data-act="project" data-id="">All projects ×</button>`:''}</p></div>
  </header>
  <p class="lede">${lede(pf)}</p>
  ${pf?'':`<div class="chips"><span class="lbl">Sessions</span>${statusChips('chip-s')||'<span class="lbl">none reporting yet</span>'}</div>`}
  <section class="block">
    <div class="sec-h"><h2>Needs you ${asks.length?`<span class="count">${asks.length}</span>`:''}</h2><button class="more" data-act="nav" data-id="asks">All asks →</button></div>
    ${asks.length?`<div class="ask-grid">${asks.map(a=>askCard(a,'main')).join('')}</div>`:'<p class="empty">Nothing waits on you.</p>'}
  </section>
  <div class="today-grid">
    <section class="block"><div class="sec-h"><h2>${pf?'Tasks':'Projects'}</h2></div>${projs.map(projectBlock).join('')||'<p class="empty">No projects yet. A session makes one when it runs <code>ws task &lt;project&gt;/&lt;task&gt;</code>.</p>'}</section>
    <section class="block"><div class="sec-h"><h2>Latest news</h2><button class="more" data-act="nav" data-id="news">All news →</button></div>${news.length?`<div class="feed narrow">${news.map(newsItem).join('')}</div>`:'<p class="empty">No news yet.</p>'}</section>
  </div>`;
}
function viewAsks(){
  const open=openAsks().sort((a,b)=>(b.blocking-a.blocking)||(b.ago-a.ago));
  const done=ASKS.filter(a=>a.answer).sort((a,b)=>a.answer.ago-b.answer.ago).slice(0,40);
  return `
  <header class="page-h"><div><h1>Needs you</h1><p class="sub">Go-aheads, decisions, reviews and unblocks your sessions are waiting on</p></div></header>
  <p class="lede">Answering here sends the answer straight back. A session holding its turn reads it within about 15 seconds. One that finished its turn gets it from its sidecar as a new message.</p>
  <section class="block"><div class="sec-h"><h2>Open ${open.length?`<span class="count">${open.length}</span>`:''}</h2></div>
    ${open.length?`<div class="ask-grid">${open.map(a=>askCard(a,'main')).join('')}</div>`:'<p class="empty">Nothing waits on you.</p>'}</section>
  <section class="block"><div class="sec-h"><h2>Answered</h2></div>
    ${done.length?`<div class="answered">${done.map(a=>{const s=S(a.s),t=a.task&&T(a.task);return `<div class="ans"><div class="ans-q">${esc(a.q)}</div><div class="ans-a">${esc(a.answer.choice)}</div><div class="ans-m">${[t?esc(t.name):'',s?`${hn(s)} · ${esc(s.name)}`:'','answered '+when(a.answer.ago)+(a.answer.ago<a.ago?`, after ${dur(a.ago-a.answer.ago)}`:'')].filter(Boolean).join(' · ')}</div></div>`}).join('')}</div>`:'<p class="empty">Nothing answered yet.</p>'}</section>`;
}
function sessionGroups(){
  const f=state.sf,q=state.q.trim().toLowerCase();
  const match=s=>(f==='all'||s.status===f)&&(!q||[s.name,ST(s)?ST(s).name:'',ST(s)&&P(ST(s).project)?P(ST(s).project).name:'',s.path,s.tmux||'',hn(s),s.agent,s.branch,s.id].join(' ').toLowerCase().includes(q));
  const out=hostOrder().map(h=>{
    const rows=SESSIONS.filter(s=>s.host===h&&match(s)).sort((a,b)=>SORD[a.status]-SORD[b.status]||a.heard-b.heard);
    if(!rows.length)return '';
    return `<div class="hgroup"><div class="hgroup-h"><b>${esc(hostInfo(h).name)}</b><span>${esc(hostInfo(h).sub)}</span></div><div class="slist">${rows.map(sessionRow).join('')}</div></div>`;
  }).join('');
  if(!SESSIONS.length)return '<p class="empty" style="margin-top:20px">No session has reported yet. Install the hooks with <code>ws install</code> on a host.</p>';
  return out||'<p class="empty" style="margin-top:20px">No session matches. Clear the filter or the search.</p>';
}
function hostNote(h){
  const open=SESSIONS.filter(s=>s.host===h&&s.status!=='ended');
  const bad=open.filter(s=>s.status==='lost'||s.status==='dead');
  if(bad.length)return {warn:true,text:bad.map(s=>`${esc(s.name)} ${s.status==='lost'?'lost contact '+ago(s.heard):'died '+ago(s.gone??s.heard)}`).join('. ')};
  if(!open.length)return {warn:false,text:'Nothing open here'};
  return {warn:false,text:'Last heard from '+ago(Math.min(...open.map(s=>s.heard)))};
}
// Reconciliation: each machine's sidecar compares the agent processes running there with the dashboard every 10 min.
const CHECK_FRESH=30;
const AGENT_NAME=a=>String(a||'claude').toLowerCase()==='codex'?'Codex':'Claude';
function hostCheck(h){
  const cs=CHECKS.filter(c=>c.host===h);
  if(!cs.length)return null;
  const newest=Math.min(...cs.map(c=>c.ago)),fresh=cs.filter(c=>c.ago<=CHECK_FRESH);
  if(!fresh.length)return {cls:'mute',text:`Last check ${ago(newest)}`,title:'No session is running there to run the check, which is normal'};
  const running=fresh.reduce((n,c)=>n+c.agents,0),missing=fresh.flatMap(c=>c.unreported.map(u=>({...u,machine:c.machine})));
  const head=`Checked ${clock(newest)} PT · `,where=fresh.length>1?` on ${fresh.length} machines`:'';
  if(missing.length)return {cls:'warn',text:`${head}${running} running${where}, ${missing.length} not reporting`,
    title:missing.map(u=>`${AGENT_NAME(u.agent)} on ${u.machine}, pid ${u.pid}${u.age_s!=null?`, running ${dur(Math.round(u.age_s/60))}`:''}`).join('\n')};
  return {cls:'ok',text:running?`${head}${running} running${where}, all on the dashboard`:`${head}no agents running${where}`};
}
function viewSessions(){
  const hosts=hostOrder().map(h=>{
    const all=SESSIONS.filter(s=>s.host===h),live=all.filter(s=>s.status!=='ended'),note=hostNote(h),chk=hostCheck(h);
    return `<div class="host"><div class="host-h"><b>${esc(hostInfo(h).name)}</b><span>${esc(hostInfo(h).sub)}</span></div>
      <div class="host-n"><span class="big">${live.length}</span> open session${live.length===1?'':'s'}${all.length>live.length?`, ${all.length-live.length} ended`:''}</div>
      <div class="host-dots">${all.sort((a,b)=>SORD[a.status]-SORD[b.status]).map(s=>`<span class="sdot" data-s="${s.status}" title="${esc(s.name)}: ${SLABEL[s.status]}"></span>`).join('')}</div>
      <p class="host-note ${note.warn?'warn':''}">${note.text}</p>
      ${chk?`<p class="host-check ${chk.cls}" data-check="${esc(h)}"${chk.title?` title="${esc(chk.title)}"`:''}>${esc(chk.text)}</p>`:''}</div>`;
  }).join('');
  return `
  <header class="page-h"><div><h1>Sessions</h1><p class="sub">Every Claude and Codex session, where it lives, and whether it is alive</p></div></header>
  ${hosts?`<div class="hosts">${hosts}</div>`:''}
  <div class="tools">
    <div class="chips"><button class="chip" data-act="sf" data-id="all" ${state.sf==='all'?'aria-pressed="true"':''}>All ${SESSIONS.length}</button>${statusChips('sf',state.sf)}</div>
    <input class="search" id="q" type="search" placeholder="Search name, task, folder, tmux" value="${esc(state.q)}" aria-label="Search sessions">
  </div>
  <div id="slist">${sessionGroups()}</div>
  <div class="legend" style="margin-top:14px"><span>Strip = last 24 h in 30-min cells</span>${LEGEND}</div>`;
}
function viewNews(){
  const filters=[['all','All'],['good','Good'],['bad','Bad'],['resolved','Resolved'],['progress','Progress'],['asks','Asks and decisions'],['auto','Auto']];
  const f=state.nf;
  const ev=EVENTS.filter(e=>visTask(e.task)).filter(e=>f==='all'||(f==='asks'?(e.kind==='ask'||e.kind==='decision'):f==='auto'?e.sys:e.kind===f));
  const days=[];ev.forEach(e=>{const l=dayLabel(e.ago);let d=days.find(x=>x.l===l);if(!d){d={l,items:[]};days.push(d)}d.items.push(e)});
  return `
  <header class="page-h"><div><h1>News</h1><p class="sub">Good and bad news worth knowing, newest first</p></div></header>
  <p class="lede">Sessions write these when something changes what you know. Items marked <span class="kind" data-k="bad">Bad<em>auto</em></span> come from the server itself, because a session that died cannot say so.</p>
  <div class="chips" style="margin-bottom:8px">${filters.map(([k,l])=>`<button class="chip" data-act="nf" data-id="${k}" ${f===k?'aria-pressed="true"':''}>${l}</button>`).join('')}</div>
  ${days.map(d=>`<h3 class="day">${d.l}</h3><div class="feed">${d.items.map(newsItem).join('')}</div>`).join('')||'<p class="empty">Nothing here.</p>'}`;
}
function viewApi(){
  return `
  <header class="page-h"><div><h1>Reporting API</h1><p class="sub">How any session on any machine keeps this page true</p></div></header>
  <div class="doc">
  <p class="lede">Sessions write two kinds of things. Hooks and a small sidecar report where a session is and whether it is alive, without the AI doing anything. The AI writes only what needs judgment: news worth knowing, asks that need you, milestones and ETAs.</p>
  <div class="flow">
    <div class="fnode"><b>Any session</b><span>Claude or Codex on the Mac, Jupiter or Horizon</span></div>
    <div class="farrows">
      <div><span class="fa">→</span>heartbeat <em>hooks and sidecar, automatic</em></div>
      <div><span class="fa">→</span>news, asks, ETAs <em>ws command, AI-written</em></div>
      <div class="back"><span class="fa">←</span>your answers and messages <em>picked up by the sidecar</em></div>
    </div>
    <div class="fnode"><b>Workspace API</b><span>Supabase. Stores everything and decides status from silence</span></div>
    <div class="fa big">→</div>
    <div class="fnode"><b>This page</b><span>You read, answer, message and resume</span></div>
  </div>

  <h2 class="doc-h">Three writes</h2>
  <div class="writes">
    <article class="wcard"><header><b>Heartbeat</b><span class="tag">automatic</span></header><p>Hooks send it at session start, on every prompt and tool call, at turn end and at session end. The sidecar pings every 5 minutes and watches the process.</p><p class="carries">Session id, agent and model, host and machine, folder, tmux pane, git branch, Remote Control id, what it is doing now, and when to expect the next one.</p></article>
    <article class="wcard"><header><b>News</b><span class="tag">AI-written</span></header><p>Something you would want to hear. A gate passed or failed, a job died, a fix landed, a number came in.</p><p class="carries">Good, bad, resolved or progress. One plain headline, with optional detail and links.</p></article>
    <article class="wcard"><header><b>Ask</b><span class="tag">AI-written</span></header><p>The session needs a go-ahead, a decision, a review or an unblock from you.</p><p class="carries">Question, options, cost and context. It can hold its turn until you answer, and your answer comes back as the command’s output.</p></article>
  </div>

  <h2 class="doc-h">The ws command</h2>
  <pre><span class="c"># once, at session start: which task this session serves (this also names it)</span>
ws task horizon-port/rl-parity

<span class="c"># milestones, set once and ticked as they pass</span>
ws plan "Restore snapshots" "Smoke gate" "5-node RL smoke" "Paired step"
ws step done "Restore snapshots" --note "11 of 11 in 9 min"

<span class="c"># ETAs for the next milestone and the whole task, each with its basis</span>
ws eta next 15:20 --measured "7 repos in 70 min"
ws eta done 2026-10-17T18:00 --estimate "two gates of half a day each" \\
    --why "restoring the snapshots took most of a day"

<span class="c"># news worth knowing</span>
ws news good "All 11 R2E-Gym snapshots restored on Horizon in 9 minutes"
ws news bad  "restore.sh stopped on a digest mismatch for the numpy image"

<span class="c"># an ask that holds the turn until you answer (polls every 10 s)</span>
ws ask go "Launch the learnability screen?" \\
    --cost "24 node-h on Jupiter" --options Go,Hold --wait 6h
<span class="c"># prints: ANSWER Go</span>

<span class="c"># a clean exit, so it never reads as a death</span>
ws end --handoff ai_memory/handoffs/2026-10-15_1430PT_rl-parity.md</pre>

  <h2 class="doc-h">What a heartbeat carries</h2>
  <pre>{
  "session_id": "3f0c9e21-7b44-4d0a-9c61-5e2a8f17d4b3",
  "event": "PreToolUse", "agent": "claude", "model": "claude-opus-5-5",
  "machine": "login1", "cwd": "/scratch/11584/lukedhlee/snowball",
  "tmux_session": "hz-rl", "branch": "lukedhlee/snowball-r2egym",
  "activity": "Bash: squeue -u lukedhlee",
  "turn_state": "running", "expect_next_by": "2026-10-15T14:52:00-07:00",
  "turn": {"role": "tool", "tool": "Bash", "input": "squeue -u lukedhlee"}
}</pre>
  <p style="margin-top:10px">The host is never in the payload. It comes from the per-host token, so a host can only write its own sessions.</p>

  <h2 class="doc-h">Endpoints</h2>
  <p>Every call is a POST to <code>/rest/v1/rpc/&lt;name&gt;</code> with the publishable key and an <code>x-ws-token</code> header.</p>
  <div class="tbl" style="margin-top:12px"><table>
    <thead><tr><th>Call</th><th>Sent by</th><th>What it does</th></tr></thead>
    <tbody>
      <tr><td><code>ws_beat</code></td><td>hooks</td><td>Updates where the session is, what it is doing and when to expect it next, and mirrors the turn</td></tr>
      <tr><td><code>ws_task</code>, <code>ws_task_update</code></td><td>ws task</td><td>Binds the session to a task, creating the project and task on first use, which also names it</td></tr>
      <tr><td><code>ws_plan</code>, <code>ws_step</code></td><td>ws plan, ws step</td><td>Sets the milestones and ticks them off</td></tr>
      <tr><td><code>ws_eta</code></td><td>ws eta</td><td>Sets the next-milestone and whole-task ETAs. Every change is kept with its reason</td></tr>
      <tr><td><code>ws_news</code></td><td>ws news</td><td>Adds a good, bad, resolved or progress item</td></tr>
      <tr><td><code>ws_ask</code>, <code>ws_ask_wait</code></td><td>ws ask</td><td>Puts an ask on your Needs-you list, and with --wait polls until you answer</td></tr>
      <tr><td><code>ws_poll</code>, <code>ws_delivered</code></td><td>sidecar</td><td>Keeps the session visible, picks up your messages and answers, and marks them delivered</td></tr>
      <tr><td><code>ws_gone</code></td><td>sidecar</td><td>The process vanished without a clean end, so the session reads as Dead</td></tr>
      <tr><td><code>ws_end</code></td><td>ws end, SessionEnd</td><td>Marks a clean end and records the handoff file</td></tr>
      <tr><td>rows</td><td>this page</td><td>Your login answers asks, queues messages, and archives or deletes. No host token can do any of these</td></tr>
    </tbody>
  </table></div>

  <h2 class="doc-h">How status is decided</h2>
  <p>The server decides session status from what it hears and when, first match wins. A dead session cannot report its own death, so silence is the signal.</p>
  <div class="tbl" style="margin-top:12px"><table>
    <thead><tr><th>Status</th><th>Rule</th></tr></thead>
    <tbody>
      <tr><td>${spill('ended')}</td><td>It ended cleanly through ws end or the SessionEnd hook, or its process exited while it was idle with nothing asked</td></tr>
      <tr><td>${spill('dead')}</td><td>Its process disappeared mid-turn or with an open ask, without a clean end</td></tr>
      <tr><td>${spill('lost')}</td><td>No contact of any kind, hook or sidecar, for 30 minutes. Something is wrong and we cannot tell what</td></tr>
      <tr><td>${spill('needs')}</td><td>It has an open ask</td></tr>
      <tr><td>${spill('silent')}</td><td>A turn is running and it is past the time its last heartbeat promised</td></tr>
      <tr><td>${spill('working')}</td><td>A turn is running inside its promised window</td></tr>
      <tr><td>${spill('idle')}</td><td>Its turn ended, nothing is asked, and its process is alive</td></tr>
    </tbody>
  </table></div>
  <p class="note">Each heartbeat says when to expect the next. Before a tool call, the hook reads that call’s timeout and adds 5 minutes, so a watcher that sleeps 15 minutes inside one Bash call never reads as silent. The sidecar pings every 5 minutes, so an idle session never drifts into Lost.</p>
  <p style="margin-top:12px">Task health follows from this. A task shows Needs you while it has an open ask, and At risk while one of its sessions is Silent, Lost or Dead. Otherwise it shows what the AI last set: On track, Blocked, Paused or Done.</p>
  <p>ETAs follow the same idea. Each one says whether it was measured from a rate (plain) or estimated (marked ~). An ETA that waits on you starts its clock at your answer. When an ETA passes before its milestone is ticked, the task shows Overdue and an auto news item goes out. Every change is kept with its reason, so slips stay visible instead of quietly moving.</p>

  <h2 class="doc-h">Reaching the API from every cluster</h2>
  <ul class="plain">
    <li>Sessions run on login nodes and the Mac, which all reach the internet over HTTPS, so they post directly. Compute nodes never report.</li>
    <li>Hooks run in the background, so a slow or broken API never stalls a session. If a call fails, ws writes it to <code>~/.ws/spool</code> and the sidecar sends it later with its original timestamp.</li>
    <li>One sidecar per session checks the process every 30 seconds, pings every 5 minutes, and delivers your messages. That is how Dead gets confirmed instead of guessed.</li>
    <li>One token per host in <code>~/.ws/config</code>, set up by <code>ws install --host &lt;name&gt;</code>. Tokens are revocable.</li>
  </ul>

  <h2 class="doc-h">Is the dashboard complete?</h2>
  <p>Every 10 minutes, each session’s sidecar lists the Claude and Codex processes running on its machine and compares them with the live sessions here. One that has run for over 2 minutes without reporting becomes a Bad news item and shows on its host’s card under Sessions, so a session with missing hooks cannot hide. A session that looks live but whose process is gone is settled automatically: ended quietly if it was idle, Dead otherwise.</p>

  <h2 class="doc-h">Looking in and talking back</h2>
  <p>Sessions started with Remote Control can be watched and typed to live in claude.ai, so this page links straight there. It cannot show claude.ai inside itself, because that is a separate site.</p>
  <p>For every session, the same hooks mirror prompts, tool calls with the head and tail of their output, and final replies, with tokens and keys redacted. That is the mirror under Conversation. Because the mirror holds what your sessions see, the backend stays private to you.</p>
  <div class="tbl" style="margin-top:12px"><table>
    <thead><tr><th>Session is</th><th>How your message reaches it</th></tr></thead>
    <tbody>
      <tr><td>${spill('working')}</td><td>It reaches the session the moment its current turn ends. Agents take your instructions only at turn boundaries, never in the middle of a tool call</td></tr>
      <tr><td>${spill('needs')}</td><td>An answer to its ask reaches it within seconds; other messages when its turn ends</td></tr>
      <tr><td>${spill('idle')}</td><td>It wakes the session within a few seconds and starts a new turn</td></tr>
      <tr><td>${spill('silent')} ${spill('lost')}</td><td>Queued. It lands only if the session recovers</td></tr>
      <tr><td>${spill('dead')} ${spill('ended')}</td><td>Cannot be delivered. Resume it first</td></tr>
    </tbody>
  </table></div>
  <p class="note">Only your login can create a message, because a message is an instruction to an agent that can run shell commands. It arrives through the hooks you installed, at a turn boundary and never mixed into a tool result, which is why the agent treats it as yours.</p>

  <h2 class="doc-h">What the skill tells the AI</h2>
  <ul class="plain">
    <li>Bind the session to a task once, at the start, and set the milestones.</li>
    <li>Give an ETA for the next milestone and the whole task, say whether it is measured or estimated, and give a reason whenever it moves.</li>
    <li>Post news when it changes what you know. Routine steps stay out.</li>
    <li>Ask whenever it needs you, with the cost in the ask, and hold the turn when nothing else can move.</li>
    <li>End with ws end and the handoff path, so a clean exit never reads as a death.</li>
  </ul>
  </div>`;
}

/* ---------- drawers ---------- */
function timeline(evs){
  if(!evs.length)return '<p class="empty">No reports yet.</p>';
  return `<ol class="tl">${evs.map(e=>{const s=e.s&&S(e.s);return `<li><span class="kind" data-k="${e.kind}">${KIND[e.kind]||esc(e.kind)}${e.sys?'<em>auto</em>':''}</span><div><div class="tl-h">${esc(e.h)}</div>${e.detail?`<div class="tl-d">${esc(e.detail)}</div>`:''}<div class="tl-m">${when(e.ago)}${s?` · ${hn(s)} · ${esc(s.name)}`:''}${links(e.links)}</div></div></li>`}).join('')}</ol>`;
}
function stepDot(m){return m==='done'?ICON.check:m==='failed'?ICON.cross:m==='needs'?'!':m==='blocked'?'–':''}
function sessCard(s){
  return `<div class="scard" data-act="session" data-id="${s.key}" role="button" tabindex="0">
    <div><div class="scard-n">${hn(s)} · ${esc(s.name)} ${spill(s.status)}</div><div class="scard-m">${s.activity?esc(s.activity)+' · ':''}${heardText(s)}</div></div>
    <button class="btn sm" data-act="copy" data-text="${esc(resume(s))}" data-label="resume command">${ICON.term}Resume</button>
  </div>`;
}
function taskDrawer(t){
  const p=P(t.project),st=tStatus(t),evs=EVENTS.filter(e=>e.task===t.id),asks=openAsks(t.id),ss=SESSIONS.filter(s=>s.task===t.id).sort((a,b)=>SORD[a.status]-SORD[b.status]);
  const done=t.steps.filter(x=>x[1]==='done').length,ev=t.last;
  return `
  <div class="dr-top"><div class="crumb">${p?`<button data-act="project" data-id="${p.id}">${esc(p.name)}</button><span>/</span>`:''}<span>Task</span></div>
    <div class="dr-actions">${vis(t)?`<button class="btn sm ghost" data-act="confirm" data-kind="archive-task" data-id="${t.id}">${ICON.archive}Archive</button>`:`<button class="btn sm" data-act="restore" data-kind="task" data-id="${t.id}">Restore</button>`}<button class="x" data-act="close" aria-label="Close">${ICON.x}</button></div></div>
  <h2 class="dr-title">${esc(t.name)}</h2>
  <div class="dr-meta">${vis(t)?tpill(st,t):'<span class="pill" data-s="ended">Archived</span>'}${ev?`<span>Last report ${ago(ev.ago)}</span>`:''}</div>
  ${state.confirm&&state.confirm.kind==='archive-task'&&state.confirm.id===t.id?confirmBar('archive-task',t.id):''}
  ${asks.length?`<section class="dr-sec"><h4>Needs you</h4>${asks.map(a=>askCard(a,'drawer')).join('')}</section>`:''}
  <section class="dr-sec"><dl class="kv"><dt>Goal</dt><dd>${esc(t.goal)||'<span style="color:var(--ink-3)">Not set</span>'}</dd><dt>Next</dt><dd>${esc(t.next)||'<span style="color:var(--ink-3)">Not set</span>'}</dd></dl></section>
  ${etaBlock(t)}
  <section class="dr-sec"><h4>Progress <span>${done} of ${t.steps.length} milestones</span></h4>
    ${t.steps.length?`<ol class="steps">${t.steps.map(([n,m,note])=>`<li data-m="${m}"><span class="st-dot">${stepDot(m)}</span><div><div class="st-name">${esc(n)}</div>${note?`<div class="st-note">${esc(note)}</div>`:''}</div></li>`).join('')}</ol>`:'<p class="empty">No milestones yet. The session sets them with <code>ws plan</code>.</p>'}</section>
  <section class="dr-sec"><h4>Sessions <span>${ss.length}</span></h4>${ss.map(sessCard).join('')||'<p class="empty">No session on this task.</p>'}</section>
  <section class="dr-sec"><h4>History</h4>${timeline(evs)}</section>`;
}
function sessionDrawer(s){
  const t=ST(s),p=t?P(t.project):null,evs=EVENTS.filter(e=>e.s===s.key),asks=ASKS.filter(a=>a.s===s.key&&!a.answer&&visTask(a.task));
  const bad=['silent','lost','dead','ended'].includes(s.status),cmd=resume(s),alt=s.status==='lost'&&s.tmux&&s.host!=='mac'?fresh(s):null;
  return `
  <div class="dr-top"><div class="crumb">${t&&p?`<button data-act="project" data-id="${p.id}">${esc(p.name)}</button><span>/</span><button data-act="task" data-id="${t.id}">${tLabel(s)}</button><span>/</span>`:''}<span>Session</span></div><button class="x" data-act="close" aria-label="Close">${ICON.x}</button></div>
  <h2 class="dr-title">${hn(s)} · ${esc(s.name)}</h2>
  <div class="dr-meta"><span class="agent">${s.agent}</span>${s.model?`<span>${esc(s.model)}</span>`:''}<span>started ${when(s.started)}</span></div>
  <div class="status-box" data-s="${s.status}">
    <div class="row">${spill(s.status)}<span>${s.status==='ended'?heardText(s):'last heard '+ago(s.heard)}</span></div>
    <p>${esc(statusNote(s))}</p>
    ${bad&&s.activity?`<p style="color:var(--ink-3);font-size:13px">Last activity: ${esc(s.activity)}</p>`:''}
  </div>
  ${convo(s)}
  ${asks.length?`<section class="dr-sec"><h4>Waiting on you</h4>${asks.map(a=>askCard(a,'drawer')).join('')}</section>`:''}
  <section class="dr-sec"><h4>Resume</h4><div class="resume">
    <button class="btn primary big" data-act="copy" data-text="${esc(cmd)}" data-label="resume command" data-resume="main">${ICON.term}Copy resume command</button>
    <div class="cmd">${esc(cmd)}</div>
    <p class="resume-hint">${resumeHint(s)}</p>
    ${alt?`<div class="cmd alt">${esc(alt)}</div>`:''}
    <div class="resume-row">
      ${alt?`<button class="btn sm" data-act="copy" data-text="${esc(alt)}" data-label="fresh-pane command" data-resume="fresh">${ICON.term}Copy fresh-pane command</button>`:''}
      <button class="btn sm" data-act="copy" data-text="${esc(s.id)}" data-label="session id">${ICON.copy}Copy session id</button>
      ${s.rc&&isLive(s)?`<a class="btn sm" href="https://claude.ai/code/${encodeURIComponent(s.rc)}" target="_blank" rel="noopener">Open in claude.ai ${ICON.ext}</a>`:''}
      ${s.handoff?`<button class="btn sm" data-act="copy" data-text="${esc(s.handoff)}" data-label="handoff path">${ICON.copy}Copy handoff path</button>`:''}
    </div></div></section>
  <section class="dr-sec"><h4>Where it lives</h4><dl class="kv">
    <dt>Host</dt><dd>${esc(hostInfo(s.host).name)} <span style="color:var(--ink-3)">${hostInfo(s.host).sub?'· '+esc(hostInfo(s.host).sub)+' ':''}· ${esc(s.machine)}</span></dd>
    <dt>Folder</dt><dd class="mono">${esc(s.path)||'—'}</dd>
    <dt>Pane</dt><dd class="mono">${s.tmux?'tmux '+esc(s.tmux)+(s.pane?` <span style="color:var(--ink-3)">(${esc(s.pane)})</span>`:''):'Terminal tab'}</dd>
    <dt>Branch</dt><dd class="mono">${esc(s.branch)||'—'}</dd>
    <dt>Session</dt><dd class="mono">${esc(s.id)}</dd>
    ${s.handoff?`<dt>Handoff</dt><dd class="mono">${esc(s.handoff)}</dd>`:''}
  </dl></section>
  <section class="dr-sec"><h4>Last 24 hours</h4>${strip(s)}<div class="strip-cap"><span>${clock(1440)} yesterday</span><span>${clock(720)}</span><span>now</span></div>
    <div class="legend">${LEGEND}</div></section>
  <section class="dr-sec"><h4>Reports from this session</h4>${timeline(evs)}</section>`;
}

/* ---------- archive ---------- */
function confirmBar(kind,id){
  let msg,label;
  if(kind.startsWith('archive')){
    const isT=kind==='archive-task',o=isT?T(id):P(id),tids=isT?[id]:TASKS.filter(t=>t.project===id&&!t.archived).map(t=>t.id);
    if(!o)return '';
    const live=SESSIONS.filter(s=>tids.includes(s.task)&&!['ended','dead'].includes(s.status)).length,asks=ASKS.filter(a=>!a.answer&&tids.includes(a.task)).length;
    msg=`Archive “${esc(o.name)}”${isT?'':` and its ${tids.length} task${tids.length===1?'':'s'}`}? It leaves every view, and its history is kept so you can restore it.`
      +(live?` ${live} running session${live>1?'s still report':' still reports'} here. ${live>1?'They keep':'It keeps'} running and ${live>1?'are':'is'} told on the next call.`:'')
      +(asks?` ${asks} open ask${asks>1?'s are':' is'} hidden with it.`:'');
    label='Archive';
  }else{
    const o=kind==='purge-task'?T(id):P(id);
    if(!o)return '';
    msg=`Delete “${esc(o.name)}” forever? Its milestones, ETAs, news, asks and ended sessions go with it. This cannot be undone.`;
    label='Delete forever';
  }
  return `<div class="confirm" role="alert"><p>${msg}</p><div class="confirm-btns"><button class="btn sm danger" data-act="do" data-kind="${kind}" data-id="${id}">${label}</button><button class="btn sm ghost" data-act="cancel">Cancel</button></div></div>`;
}
async function setArchived(kind,id,val){
  const o=kind==='task'?T(id):P(id);if(!o)return;
  state.confirm=null;
  const {error}=await sb.from(kind==='task'?'tasks':'projects').update({archived_at:val?new Date().toISOString():null}).eq('id',id);
  if(error){toast(`Could not ${val?'archive':'restore'} ${o.name}`,error.message,true);render();return}
  o.archived=val;   // shown at once; the refetch confirms it
  if(val){
    if(kind==='project'&&state.project===id)state.project=null;
    const d=state.drawer;
    if(d&&d.kind==='task'&&(d.id===id||(T(d.id)&&T(d.id).project===id)))closeDrawer();
    toast(`Archived ${o.name}`,null,true,`<button class="toast-btn" data-act="restore" data-kind="${kind}" data-id="${id}">Undo</button>`);
  }else toast(`Restored ${o.name}`);
  render();refreshSoon(0);
}
async function purge(kind,id){
  const o=kind==='task'?T(id):P(id);if(!o)return;
  const {error}=await sb.rpc('ws_admin_purge',{p_kind:kind,p_id:id});
  if(error){toast(`Could not delete ${o.name}`,error.message,true);return}
  state.confirm=null;closeDrawer();toast(`Deleted ${o.name} forever`);await refresh();
}
function viewArchived(){
  const c=state.confirm;
  const ap=PROJECTS.filter(p=>p.archived),at=TASKS.filter(t=>t.archived&&P(t.project)&&!P(t.project).archived);
  const row=(kind,o,meta)=>`<div class="arow" data-archived="${o.id}"><div><div class="arow-n">${esc(o.name)}</div><div class="arow-m">${meta}</div></div>
    <div class="arow-btns"><button class="btn sm" data-act="restore" data-kind="${kind}" data-id="${o.id}">Restore</button><button class="btn sm danger" data-act="confirm" data-kind="purge-${kind}" data-id="${o.id}">Delete forever</button></div>
    ${c&&c.kind==='purge-'+kind&&c.id===o.id?confirmBar('purge-'+kind,o.id):''}</div>`;
  const rows=[...ap.map(p=>row('project',p,`Project · ${TASKS.filter(t=>t.project===p.id).length} tasks`)),
    ...at.map(t=>row('task',t,`Task in ${esc(P(t.project).name)} · ${t.verdict?'closed, '+esc(t.verdict):esc(t.next)}`))];
  return `
  <header class="page-h"><div><h1>Archived</h1><p class="sub">Projects and tasks you removed from view</p></div></header>
  <p class="lede">Archiving hides a project or task everywhere but keeps its history, so you can bring it back. Deleting forever is only offered from here, so nothing disappears in one click.</p>
  <section class="block">${rows.length?`<div class="arch">${rows.join('')}</div>`:'<p class="empty">Nothing archived.</p>'}</section>`;
}

/* ---------- looking in and talking back ---------- */
function delivery(s){
  const hold=ASKS.some(a=>a.s===s.key&&!a.answer&&a.blocking);
  if(s.status==='ended')return {ok:false,text:'This session has ended. Resume it first, then message it.'};
  if(s.status==='dead')return {ok:false,text:'Its process is gone, so nothing can deliver a message. Resume it first.'};
  if(s.status==='lost')return {ok:true,text:`Queued. Nothing has been heard from it for ${dur(s.heard)}, so this lands only if its sidecar comes back.`};
  if(s.status==='silent')return {ok:true,text:'Queued. It is mid-turn but not responding, so this lands only if it recovers.'};
  if(s.status==='needs'&&hold)return {ok:true,text:'It is waiting for your answer to its ask. Answers reach it within seconds; other messages when its turn ends.'};
  if(s.status==='working')return {ok:true,text:'It is mid-turn, so this reaches it the moment the turn ends. Agents only take your instructions at turn boundaries.'};
  return {ok:true,text:s.agent==='Codex'?'It is idle, so its sidecar starts a turn with this within a minute.':'It is idle, so this wakes it within a few seconds.'};
}
function convoItems(s){
  const c=CONVO[s.id];if(!c)return null;
  // The sidecar delivers a message as "[Workspace] Message from Luke: <body>" and the prompt hook mirrors that back as a
  // you-turn via workspace (redacted and clipped), so match on the body's opening words and show it once.
  const norm=x=>String(x||'').replace(/\s+/g,' ').trim();
  const keys=c.msgs.map(m=>norm(m.body).slice(0,160)).filter(Boolean),out=[];
  for(const t of c.turns){
    const a=agoOf(t.ts);
    if(t.role==='tool'){
      const tool=t.tool||'Tool';
      if(t.output!=null){   // a returned call: attach its output to the call it answers, if that is shown
        let hit=null;
        for(let i=out.length-1;i>=Math.max(0,out.length-6);i--){const p=out[i];if(p.w==='tool'&&p.o==null&&p.tool===tool&&(t.input==null||t.input===p.c)){hit=p;break}}
        if(hit){hit.o=t.output;continue}
      }
      out.push({w:'tool',a,ts:t.ts,tool,c:t.input||'',o:t.output??null});
    }else if(t.role==='you'){
      if(String(t.via||'').toLowerCase()==='workspace'&&keys.some(k=>norm(t.text).includes(k)))continue;   // already shown as your message
      out.push({w:'you',a,ts:t.ts,x:t.text||'',via:t.via||'terminal'});
    }else out.push({w:t.role==='system'?'sys':'ai',a,ts:t.ts,x:t.text||''});
  }
  for(const m of c.msgs)out.push({w:'you',a:agoOf(m.ts),ts:m.ts,x:m.body,via:'Workspace',st:m.delivered_at?'delivered':'queued',ans:!!m.ask_id,mid:m.id});
  out.sort((x,y)=>tms(x.ts)-tms(y.ts));
  const last=out[out.length-1];
  if(last&&last.w==='tool'&&last.o==null&&['working','needs','silent'].includes(s.status))last.run=true;
  return out;
}
function convoBody(s){
  const items=convoItems(s),who=s.agent;
  if(!items)return '<p class="m-meta" style="text-align:center">Loading…</p>';
  if(!items.length)return `<p class="m-meta" style="text-align:center">${s.status==='ended'?'Nothing mirrored. Ended sessions keep their turns for 30 days.':'No turns mirrored yet.'}</p>`;
  const more=CONVO[s.id].turns.length>=TURN_LIMIT?`<p class="m-more">Showing the last ${TURN_LIMIT} turns</p>`:'';
  return more+items.map(m=>{
    if(m.w==='you')return `<div class="m you"${m.mid?` data-msg="${m.mid}"`:''}><div class="bubble">${esc(m.x)}</div><div class="m-meta">You · ${m.ans?'answer ':''}via ${esc(m.via)} · ${stamp(m.a)}${m.st==='queued'?' · <span class="q">queued</span>':m.st==='delivered'?' · <span class="d">delivered</span>':''}</div></div>`;
    if(m.w==='ai')return `<div class="m ai"><div class="m-who">${who} · ${stamp(m.a)}</div><div class="m-text">${esc(m.x)}</div></div>`;
    if(m.w==='tool')return `<div class="m tool"><div class="cl"><b>${esc(m.tool)}</b>${esc(m.c)}</div>${m.run?`<div class="out run">running</div>`:m.o?`<div class="out">${esc(m.o)}</div>`:''}</div>`;
    return `<div class="m sys">${esc(m.x)}</div>`;
  }).join('');
}
function rcNote(s){return s.rc&&isLive(s)?`<div class="rc-note"><span>Remote Control is on, so you can also watch it live and type to it in claude.ai.</span><a class="btn sm" href="https://claude.ai/code/${encodeURIComponent(s.rc)}" target="_blank" rel="noopener">Open live ${ICON.ext}</a></div>`:''}
function composer(s,ctx){
  const d=delivery(s),id=`msg-${ctx}-${s.key}`;
  return `<div class="composer"><label for="${id}">Message ${hn(s)} · ${esc(s.name)}</label>
    <textarea id="${id}" rows="2" maxlength="8000" placeholder="${d.ok?'e.g. Skip numpy for now and report what you have. Enter sends, Shift+Enter adds a line':'Resume it first'}" ${d.ok?'':'disabled'}></textarea>
    <div class="composer-row"><p>${esc(d.text)}</p><button class="btn primary sm" data-act="msg" data-id="${s.key}" ${d.ok?'':'disabled'}>Send</button></div></div>`;
}
function convo(s){
  ensureConvo(s.id);
  return `<section class="dr-sec"><h4>Conversation <button class="more" data-act="chat" data-id="${s.key}">Open full view →</button></h4>
    ${rcNote(s)}<div class="convo" data-sid="${esc(s.id)}" data-where="drawer">${convoBody(s)}</div>${composer(s,'d')}</section>`;
}
function preview(s){
  const t=s.lastTurn;
  if(!t)return {t:'No turns yet',a:s.heard};
  return {t:t.role==='you'?'You: '+(t.text||''):t.role==='tool'?'$ '+(t.input||t.tool||''):(t.text||''),a:agoOf(t.ts)};
}
function viewChat(){
  const list=[...SESSIONS].sort((a,b)=>(SORD[a.status]-SORD[b.status])||(a.heard-b.heard));
  const head=`<header class="page-h"><div><h1>Conversations</h1><p class="sub">Read what any session has been doing, and talk to it</p></div></header>`;
  if(!list.length)return head+'<p class="empty" style="margin-top:16px">No session has reported yet.</p>';
  if(!state.chat||!S(state.chat))state.chat=(list.find(s=>s.lastTurn&&isLive(s))||list[0]).key;
  const s=S(state.chat);
  ensureConvo(s.id);
  return `${head}
  <div class="chat">
    <nav class="clist" aria-label="Sessions" data-chat="${esc(s.key)}">${list.map(x=>{const p=preview(x);return `<button class="citem ${x.status==='ended'?'quiet':''}" data-act="chat" data-id="${x.key}" ${x.key===s.key?'aria-current="true"':''}>
      <span class="sdot" data-s="${x.status}" title="${SLABEL[x.status]}"></span><span class="ci-n">${hn(x)} · ${esc(x.name)}</span><span class="ci-t">${dayKey(p.a)===dayKey(0)?clock(p.a):dayLabel(p.a).replace(/^\w+ /,'')}</span>
      <span class="ci-p">${esc(p.t)}</span></button>`}).join('')}</nav>
    <section class="cpane">
      <div class="ch-h"><div><div class="ch-name">${hn(s)} · ${esc(s.name)} ${spill(s.status)}</div>
        <div class="ch-sub">${tLabel(s)} · ${s.agent} · ${s.tmux?'tmux '+esc(s.tmux):'Terminal tab'} on ${esc(s.machine)} · ${heardText(s)}</div></div>
        <div class="ch-btns"><button class="btn sm" data-act="copy" data-text="${esc(resume(s))}" data-label="resume command">${ICON.term}Resume</button><button class="btn sm ghost" data-act="session" data-id="${s.key}">Details</button></div></div>
      ${rcNote(s)}
      <div class="convo" data-sid="${esc(s.id)}" data-where="main">${convoBody(s)}</div>
      ${composer(s,'c')}
    </section>
  </div>`;
}
async function sendMsg(key,btn){
  const s=S(key),box=btn&&btn.closest('.composer'),ta=box?box.querySelector('textarea'):null,v=ta?ta.value.trim():'';
  if(!s)return;
  if(!v){if(ta)ta.focus();return}
  btn.disabled=true;
  const {data,error}=await sb.from('messages').insert({session_id:s.id,body:v}).select('id,ts,body,ask_id,delivered_at,delivered_via').single();
  btn.disabled=false;
  if(error){toast('Could not send the message',error.message,true);return}
  ta.value='';
  const c=CONVO[s.id];if(c&&!c.msgs.some(m=>m.id===data.id))c.msgs.push(data);
  paint();
  toast(`Sent to ${hn(s)} · ${s.name}`,delivery(s).text);
}

/* ---------- render ---------- */
const liveText=()=>OFFLINE?'Offline, retrying':STATS.rt==='SUBSCRIBED'?'Live':STATS.rt==='ERROR'?'Refreshing every 30 s':'Connecting';
function footInner(){
  const live=!OFFLINE&&STATS.rt==='SUBSCRIBED';
  return `<p><span class="live ${live?'':'off'}" data-live>${liveText()}</span> · Times are Pacific</p>
    <p>Signed in as <b>${esc(USER)}</b> · <button data-act="signout">Sign out</button></p>`;
}
function renderLive(){
  const live=!OFFLINE&&STATS.rt==='SUBSCRIBED';
  document.querySelectorAll('[data-live]').forEach(el=>{el.classList.toggle('off',!live);el.textContent=liveText()});
}
function renderSide(){
  const views=[['today','Today',ICON.today],['asks','Needs you',ICON.asks],['sessions','Sessions',ICON.sessions],['chat','Conversations',ICON.chat],['news','News',ICON.news],['api','Reporting API',ICON.api],['archived','Archived',ICON.archive]];
  const na=openAsks().length,live=SESSIONS.filter(s=>s.status!=='ended').length,today=EVENTS.filter(e=>dayKey(e.ago)===dayKey(0)&&visTask(e.task)).length;
  const narch=PROJECTS.filter(p=>p.archived).length+TASKS.filter(t=>t.archived&&P(t.project)&&!P(t.project).archived).length;
  const badge={asks:na?`<span class="badge hot">${na}</span>`:'',sessions:`<span class="badge">${live}</span>`,news:`<span class="badge">${today}</span>`,archived:narch?`<span class="badge">${narch}</span>`:''};
  $('#nav').innerHTML=views.map(([id,l,ic])=>`<button data-act="nav" data-id="${id}" ${state.view===id&&!(id==='today'&&state.project)?'aria-current="page"':''}>${ic}<span>${l}</span>${badge[id]||''}</button>`).join('');
  $('#plist').innerHTML=PROJECTS.filter(p=>!p.archived).map(p=>{
    const active=TASKS.filter(t=>t.project===p.id&&!t.archived&&!['done','paused'].includes(tStatus(t))).length;
    return `<button data-act="project" data-id="${p.id}" ${state.view==='today'&&state.project===p.id?'aria-current="page"':''}><span class="sdot" data-s="${pHealth(p)}"></span><span class="pl-n">${esc(p.name)}</span><span class="pl-c">${active}</span></button>`;
  }).join('')||'<p class="side-foot">None yet</p>';
  $('#sidefoot').innerHTML=footInner();
}
const VIEWS={today:viewToday,asks:viewAsks,sessions:viewSessions,chat:viewChat,news:viewNews,api:viewApi,archived:viewArchived};
// Re-rendering must not eat what Luke is typing or reading: keep drafts, open reply boxes, focus and convo scroll.
function snapshot(){
  const cl=$('#main .clist');
  const snap={vals:{},open:[],focus:null,convo:{},drawerTop:$('#drawer').scrollTop,list:cl?{top:cl.scrollTop,chat:cl.dataset.chat}:null};
  document.querySelectorAll('#main textarea[id],#main input[id],#drawer textarea[id]').forEach(el=>{
    snap.vals[el.id]=el.value;
    const r=el.closest('.ask-reply');if(r&&!r.hidden)snap.open.push(el.id);
  });
  const a=document.activeElement;
  if(a&&a.id&&a.matches('textarea,input'))snap.focus={id:a.id,s:a.selectionStart,e:a.selectionEnd};
  document.querySelectorAll('.convo[data-sid]').forEach(c=>{snap.convo[c.dataset.where]={sid:c.dataset.sid,top:c.scrollTop,bottom:c.scrollHeight-c.scrollTop-c.clientHeight<48}});
  return snap;
}
function restore(snap){
  for(const [id,v] of Object.entries(snap.vals)){const el=document.getElementById(id);if(el&&v&&!el.disabled)el.value=v}
  snap.open.forEach(id=>{const el=document.getElementById(id);if(el)el.closest('.ask-reply').hidden=false});
  document.querySelectorAll('.convo[data-sid]').forEach(c=>{const o=snap.convo[c.dataset.where];c.scrollTop=o&&o.sid===c.dataset.sid&&!o.bottom?o.top:c.scrollHeight});
  if(state.drawer)$('#drawer').scrollTop=snap.drawerTop;
  const cl=$('#main .clist'),cur=cl&&cl.querySelector('[aria-current="true"]');
  if(cl){
    if(snap.list)cl.scrollTop=snap.list.top;
    if(cur&&(!snap.list||snap.list.chat!==cl.dataset.chat)&&(cur.offsetTop<cl.scrollTop||cur.offsetTop+cur.offsetHeight>cl.scrollTop+cl.clientHeight))cl.scrollTop=cur.offsetTop-8;
  }
  if(snap.focus){const el=document.getElementById(snap.focus.id);if(el&&document.activeElement!==el)try{el.focus({preventScroll:true});el.setSelectionRange(snap.focus.s,snap.focus.e)}catch(e){}}
}
function paint(){
  const snap=snapshot();
  renderSide();
  $('#main').innerHTML=VIEWS[state.view]()+`<footer class="foot">${footInner()}</footer>`;
  if(state.drawer)renderDrawer();
  restore(snap);
}
const render=paint;
function go(view){
  state.view=VIEWS[view]?view:'today';state.confirm=null;
  if(state.view!=='today')state.project=null;
  try{if(location.hash!=='#'+state.view)location.hash=state.view}catch(e){}
  render();window.scrollTo(0,0);
}
function renderDrawer(){
  const d=state.drawer,el=$('#drawer');
  if((d.kind==='task'&&!T(d.id))||(d.kind==='session'&&!S(d.id))){closeDrawer();return}
  el.innerHTML=d.kind==='task'?taskDrawer(T(d.id)):sessionDrawer(S(d.id));
  el.setAttribute('aria-label',d.kind==='task'?'Task details':'Session details');
}
function openDrawer(kind,id){
  state.drawer={kind,id};state.confirm=null;renderDrawer();
  const el=$('#drawer');el.classList.add('on');$('#scrim').classList.add('on');el.scrollTop=0;
  const c=el.querySelector('.convo');if(c)c.scrollTop=c.scrollHeight;
  try{el.focus({preventScroll:true})}catch(e){}
}
function closeDrawer(){state.drawer=null;$('#drawer').classList.remove('on');$('#scrim').classList.remove('on')}

/* ---------- actions ---------- */
let toastTimer;
function toast(msg,detail,long,action){
  const el=$('#toast');el.innerHTML=esc(msg)+(action||'')+(detail?`<code>${esc(detail)}</code>`:'');el.classList.add('on');
  clearTimeout(toastTimer);toastTimer=setTimeout(()=>el.classList.remove('on'),long?9000:3800);
}
function copy(text,label){
  const done=()=>toast(`Copied ${label}`,text);
  const fallback=()=>{
    let ok=false;
    try{const ta=document.createElement('textarea');ta.value=text;ta.setAttribute('readonly','');ta.style.position='fixed';ta.style.opacity='0';document.body.appendChild(ta);ta.select();ok=document.execCommand('copy');ta.remove()}catch(e){}
    ok?done():toast('This view blocks the clipboard. Select the text below.',text,true);
  };
  try{navigator.clipboard.writeText(text).then(done,fallback)}catch(e){fallback()}
}
async function answer(id,choice){
  const a=ASKS.find(x=>x.id===id);if(!a||a.answer||!choice)return;
  const s=S(a.s);
  a.answer={choice,ago:0};render();   // shown at once; the refetch confirms it
  const {data,error}=await sb.from('asks').update({answer:choice}).eq('id',id).is('answer',null).select('id');
  if(error||!data||!data.length){
    a.answer=null;toast(error?'Could not send the answer':'This ask was already answered',error?error.message:null,true);refreshSoon(0);return;
  }
  const how=!s?'Recorded.':!isLive(s)?'Its session is not running, so the answer is recorded for when you resume it.'
    :a.blocking&&s.status==='needs'?'It is holding its turn, so it reads this within about 15 seconds.':delivery(s).text;
  toast(`Sent “${choice}”${s?` to ${hn(s)} · ${s.name}`:''}`,how);
  refreshSoon(0);
}

document.addEventListener('click',e=>{
  if(e.target.closest('a[href]'))return;
  const el=e.target.closest('[data-act]');if(!el)return;
  const act=el.dataset.act,id=el.dataset.id;
  if(act==='nav'){closeDrawer();go(id)}
  else if(act==='project'){closeDrawer();state.project=id||null;state.view='today';try{if(location.hash!=='#today')location.hash='today'}catch(err){}render();window.scrollTo(0,0)}
  else if(act==='task')openDrawer('task',id);
  else if(act==='session')openDrawer('session',id);
  else if(act==='close')closeDrawer();
  else if(act==='copy')copy(el.dataset.text,el.dataset.label);
  else if(act==='answer')answer(id,el.dataset.opt);
  else if(act==='reply'){const box=el.closest('.ask').querySelector('.ask-reply');box.hidden=!box.hidden;if(!box.hidden)box.querySelector('textarea').focus()}
  else if(act==='send'){const ta=el.closest('.ask').querySelector('textarea'),v=ta.value.trim();if(!v){ta.focus();return}answer(id,v)}
  else if(act==='confirm'){state.confirm={kind:el.dataset.kind,id};render()}
  else if(act==='cancel'){state.confirm=null;render()}
  else if(act==='do'){const k=el.dataset.kind;el.disabled=true;if(k==='archive-task')setArchived('task',id,true);else if(k==='archive-project')setArchived('project',id,true);else if(k==='purge-task')purge('task',id);else if(k==='purge-project')purge('project',id)}
  else if(act==='restore')setArchived(el.dataset.kind,id,false);
  else if(act==='msg')sendMsg(id,el);
  else if(act==='chat'){closeDrawer();state.chat=id;if(state.view==='chat')render();else go('chat');const t=$('#main .composer textarea');if(t&&!t.disabled)try{t.focus({preventScroll:true})}catch(err){}}
  else if(act==='sf'){state.sf=id;render()}
  else if(act==='chip-s'){state.sf=id;go('sessions')}
  else if(act==='nf'){state.nf=id;render()}
  else if(act==='signout')signOut();
  else if(act==='retry')boot();
});
document.addEventListener('keydown',e=>{
  if(e.key==='Escape'&&state.drawer){closeDrawer();return}
  if(e.key==='Enter'&&!e.shiftKey&&!e.isComposing&&e.target.matches('.composer textarea')){e.preventDefault();const b=e.target.closest('.composer').querySelector('[data-act="msg"]');if(b)b.click();return}
  if((e.key==='Enter'||e.key===' ')&&e.target.matches('[role="button"][data-act]')){e.preventDefault();e.target.click()}
});
document.addEventListener('input',e=>{if(e.target.id==='q'){state.q=e.target.value;$('#slist').innerHTML=sessionGroups()}});
$('#scrim').addEventListener('click',closeDrawer);
window.addEventListener('hashchange',()=>{const h=location.hash.slice(1);if(VIEWS[h]&&h!==state.view&&READY){state.view=h;if(h!=='today')state.project=null;render()}});

/* ---------- data: load, Realtime, the clock ---------- */
const must=r=>{if(r.error)throw r.error;return r.data};
const fetchConvo=sid=>Promise.all([
  sb.from('turns').select('id,ts,role,via,text,tool,input,output').eq('session_id',sid).order('id',{ascending:false}).limit(TURN_LIMIT).then(must),
  sb.from('messages').select('id,ts,body,ask_id,delivered_at,delivered_via').eq('session_id',sid).order('id',{ascending:false}).limit(MSG_LIMIT).then(must)
]).then(([t,m])=>({turns:t.reverse(),msgs:m.reverse()}));
const shownSessions=()=>[...new Set([state.view==='chat'?state.chat:null,state.drawer&&state.drawer.kind==='session'?state.drawer.id:null].filter(Boolean))];
const convoLoading=new Set();
function ensureConvo(sid){
  const c=CONVO[sid];
  if((c&&c.gen===GEN)||convoLoading.has(sid))return;
  convoLoading.add(sid);
  fetchConvo(sid).then(r=>{CONVO[sid]={...r,gen:GEN}},err=>{console.error(err);CONVO[sid]={...(CONVO[sid]||{turns:[],msgs:[]}),gen:GEN}})
    .finally(()=>{convoLoading.delete(sid);if(READY&&shownSessions().includes(sid))paint()});
}
async function load(){
  const shown=shownSessions();
  const [pr,tk,ss,as,ev,cv,hc]=await Promise.all([
    sb.from('projects').select('*').order('created_at').order('name').then(must),
    sb.from('v_tasks').select('*').order('created_at').then(must),
    sb.from('v_sessions').select('*').order('started_at',{ascending:false}).limit(500).then(must),
    sb.from('asks').select('*').order('ts',{ascending:false}).limit(500).then(must),
    sb.from('events').select('*').order('ts',{ascending:false}).limit(500).then(must),
    Promise.all(shown.map(fetchConvo)),
    sb.from('host_checks').select('*').then(must)]);
  NOW=Date.now();GEN++;STATS.loads++;
  PROJECTS=pr.map(r=>({id:r.id,slug:r.slug,name:r.name,blurb:r.blurb||'',archived:!!r.archived_at}));
  TASKS=tk.map(mapTask);SESSIONS=ss.map(mapSession);ASKS=as.map(mapAsk);EVENTS=ev.map(mapEvent);
  CHECKS=hc.map(r=>({host:r.host,machine:r.machine,ago:agoOf(r.at),agents:r.agents||0,tracked:r.tracked||0,unreported:Array.isArray(r.unreported)?r.unreported:[]}));
  PIDX=new Map(PROJECTS.map(x=>[x.id,x]));TIDX=new Map(TASKS.map(x=>[x.id,x]));SIDX=new Map(SESSIONS.map(x=>[x.key,x]));
  shown.forEach((sid,i)=>{CONVO[sid]={...cv[i],gen:GEN}});
}
let loading=null,again=false;
async function refresh(){
  if(!USER)return;
  if(loading){again=true;return loading}
  loading=(async()=>{
    try{await load();OFFLINE=false;READY=true;document.documentElement.dataset.ready='1';paint()}
    catch(e){console.error('workspace: load failed',e);OFFLINE=true;renderLive()}
  })();
  await loading;loading=null;
  if(again){again=false;return refresh()}
}
let soonTimer;
function refreshSoon(ms=300){clearTimeout(soonTimer);soonTimer=setTimeout(refresh,ms)}
let channel=null,clockTimer=null;
function subscribe(){
  if(channel)return;
  channel=sb.channel('workspace-site');
  for(const table of ['projects','tasks','milestones','sessions','events','asks','messages','turns','host_checks'])
    channel.on('postgres_changes',{event:'*',schema:'public',table},p=>{
      const r=p.new&&Object.keys(p.new).length?p.new:p.old||{};
      STATS.realtime++;STATS.seen.push(`${table}:${r.id??''}`);if(STATS.seen.length>200)STATS.seen.shift();
      if(STATS.rt==='ERROR'){STATS.rt='SUBSCRIBED';renderLive()}
      refreshSoon(300);
    });
  // Realtime reports trouble (e.g. its per-tenant rate limit) as a system message; the 30 s clock keeps data fresh meanwhile.
  channel.on('system',{},p=>{if(p&&p.status==='error'){STATS.rtError=p.message||'error';STATS.rt='ERROR';renderLive();refreshSoon(0)}});
  channel.subscribe(st=>{const was=STATS.rt;STATS.rt=st;renderLive();if(st==='SUBSCRIBED'&&was!=='SUBSCRIBED'&&READY)refreshSoon(0)});
  clockTimer=setInterval(()=>{STATS.timer++;refresh()},30000);
}
function teardown(){
  if(channel){sb.removeChannel(channel);channel=null}
  clearInterval(clockTimer);clockTimer=null;STATS.rt='closed';
  READY=false;delete document.documentElement.dataset.ready;
  PROJECTS=TASKS=SESSIONS=ASKS=EVENTS=CHECKS=[];PIDX=new Map();TIDX=new Map();SIDX=new Map();
  for(const k of Object.keys(CONVO))delete CONVO[k];
}
document.addEventListener('visibilitychange',()=>{if(document.visibilityState==='visible'&&READY)refreshSoon(0)});

/* ---------- sign-in gate ---------- */
function gate(kind,info){
  closeDrawer();$('#app').hidden=true;
  const g=$('#gate');g.hidden=false;GATE=kind;document.documentElement.dataset.state=kind;
  const card=body=>`<div class="gate"><div class="gate-card"><div class="brand">${MARK}<div><b>Workspace</b><small>Projects, tasks, sessions</small></div></div>${body}</div></div>`;
  if(kind==='login'){
    g.innerHTML=card(`<h1>Sign in</h1><p>We email you a one-time link. Open it in this browser to come back signed in.</p>
      <form id="login-form"><label for="email">Email</label><input id="email" type="email" autocomplete="email" required placeholder="you@example.com">
      <button class="btn primary big" type="submit">Email me a sign-in link</button></form>
      <div class="gate-msg ${info&&info.bad?'bad':''}" id="gate-msg" ${info&&info.text?'':'hidden'}>${esc(info&&info.text)}</div>
      <p class="gate-foot">Only the admin account sees any data. Times are Pacific.</p>`);
    $('#login-form').addEventListener('submit',sendLink);
  }else if(kind==='noaccess'){
    g.innerHTML=card(`<h1>This account has no access</h1><p>You are signed in as <b>${esc(USER)}</b>, which is not the Workspace admin, so there is nothing to show. Sign out and sign in with the admin email.</p>
      <button class="btn primary big" data-act="signout">Sign out</button>`);
  }else{
    g.innerHTML=card(`<h1>Can’t reach the Workspace database</h1><p>${esc(info||'The request failed.')}</p>
      <div class="confirm-btns"><button class="btn primary" data-act="retry">Try again</button><button class="btn ghost" data-act="signout">Sign out</button></div>`);
  }
}
async function sendLink(e){
  e.preventDefault();
  const email=$('#email').value.trim().toLowerCase(),msg=$('#gate-msg'),btn=e.target.querySelector('button');
  if(!email)return;
  btn.disabled=true;msg.hidden=false;msg.className='gate-msg';msg.textContent='Sending…';
  const {error}=await sb.auth.signInWithOtp({email,options:{emailRedirectTo:location.origin+location.pathname}});
  btn.disabled=false;
  if(error){msg.className='gate-msg bad';msg.textContent=error.message;return}
  msg.className='gate-msg ok';msg.innerHTML=`Check <b>${esc(email)}</b> for a sign-in link. Open it in this browser.`;
}
async function signOut(){await sb.auth.signOut();onAuth(null)}
async function boot(){
  let admin;
  try{admin=must(await sb.rpc('ws_is_admin'))}catch(e){gate('error',e.message||String(e));return}
  if(!admin){teardown();gate('noaccess');return}
  $('#gate').hidden=true;$('#app').hidden=false;GATE=null;document.documentElement.dataset.state='app';
  subscribe();await refresh();
}
function onAuth(session){
  const email=session&&session.user?session.user.email:null;
  if(!email){if(USER===null&&GATE==='login')return;USER=null;teardown();gate('login',urlError());return}
  if(email===USER)return;   // a token refresh, not a new sign-in
  USER=email;boot();
}
function urlError(){
  const q=new URLSearchParams(location.search),h=new URLSearchParams(location.hash.slice(1));
  const d=q.get('error_description')||h.get('error_description');
  return d?{bad:true,text:'That sign-in link did not work: '+d}:null;
}
if(LOCAL)window.__wsTestSignIn=async(email,password)=>{const {error}=await sb.auth.signInWithPassword({email,password});if(error)throw new Error(error.message);return true};

(async function init(){
  let h='';try{h=location.hash.slice(1)}catch(e){}if(VIEWS[h])state.view=h;
  const {data}=await sb.auth.getSession();
  sb.auth.onAuthStateChange((ev,session)=>setTimeout(()=>onAuth(session),0));   // never await Supabase inside this callback
  onAuth(data.session);
})();
