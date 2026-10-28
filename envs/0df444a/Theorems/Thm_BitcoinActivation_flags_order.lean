-- Prove2me | Theorems.Thm_BitcoinActivation_flags_order
-- name    : BitcoinActivation.flags_order
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:14:48.168055+00:00
-- url     : https://prove2.me/theorems/1edc4264-67d9-424c-813c-58ab961743a8
-- title:
--   The height-gated flags activate in a fixed order
-- statement:
--   For every height, in the flags of an ordinary block: `CHECKLOCKTIMEVERIFY` implies `DERSIG`, `CHECKSEQUENCEVERIFY` implies `CHECKLOCKTIMEVERIFY`, and `NULLDUMMY` implies `CHECKSEQUENCEVERIFY` — the order $363{,}725 < 388{,}381 < 419{,}328 < 481{,}824$ of the activation heights.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_order (height : Nat) :
    let f := BitcoinActivation.blockScriptFlags height .none
    (f.cltv = true → f.dersig = true) ∧ (f.csv = true → f.cltv = true) ∧
    (f.nulldummy = true → f.csv = true) := by sorry
