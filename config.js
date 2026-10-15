/* Where the site reads from. Served from this machine it uses the local Supabase stack, anywhere else the cloud
   project. Both keys are publishable keys: public by design, every row stays behind the login and row-level security. */
window.WS_CONFIG = (function () {
  const local = ['localhost', '127.0.0.1'].includes(location.hostname);
  return local
    ? {env: 'local', url: 'http://127.0.0.1:54321', key: 'sb_publishable_ACJWlzQHlZjBrEguHvfOxg_3BJgxAaH'}
    : {env: 'cloud', url: 'https://qxobkhkjvlmfuelyrdmr.supabase.co', key: 'sb_publishable_BY6Wp3MzhCO_DpM0sMKLBg_p-xGpoSQ'};
})();
