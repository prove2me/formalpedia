-- Prove2me | Theorems.Thm_BitcoinActivation_flags_before_bip66
-- name    : BitcoinActivation.flags_before_bip66
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:14:29.871118+00:00
-- url     : https://prove2.me/theorems/0163ec62-173e-4174-8f05-487a2746c8e9
-- title:
--   Before BIP66 an ordinary block enforces only the base flags
-- statement:
--   For every height $h < 363{,}725$, the flags of an ordinary block are exactly `P2SH | WITNESS | TAPROOT`: none of the height-gated rules is active yet.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_before_bip66 (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .none = BitcoinActivation.baseFlags := by sorry
