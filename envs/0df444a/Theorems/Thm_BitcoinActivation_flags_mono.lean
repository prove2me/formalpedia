-- Prove2me | Theorems.Thm_BitcoinActivation_flags_mono
-- name    : BitcoinActivation.flags_mono
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:15:37.302626+00:00
-- url     : https://prove2.me/theorems/b7bab6b5-7739-4ea1-b9f1-6d61c104862a
-- title:
--   Soft forks only add script rules
-- statement:
--   For all heights $h_1 \le h_2$, every script-verification flag enforced for an ordinary block at height $h_1$ is enforced at height $h_2$:
--   $$\mathrm{blockScriptFlags}(h_1, \mathrm{none}) \subseteq \mathrm{blockScriptFlags}(h_2, \mathrm{none}),$$
--   where inclusion is pointwise over the seven flags `P2SH`, `WITNESS`, `TAPROOT`, `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY`, and `blockScriptFlags` is the transcription of `GetBlockScriptFlags` at mainnet heights.
--
--   This is the structural content of buried deployments: the ruleset in force is a non-decreasing function of height, so "the rules at height $h$" is well defined and a rule, once enforced, is never relaxed for ordinary blocks. The two hash-keyed exception blocks are the only departures, and are covered by separate theorems.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_mono (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags h₁ .none)
      (BitcoinActivation.blockScriptFlags h₂ .none) := by sorry
