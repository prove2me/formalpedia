-- Prove2me | Theorems.Thm_BitcoinActivation_bip16_exception
-- name    : BitcoinActivation.bip16_exception
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:14:57.464995+00:00
-- url     : https://prove2.me/theorems/8b7682d3-d02e-4f70-a465-a27141d5ea69
-- title:
--   The BIP16 exception block enforces no script flags
-- statement:
--   For every height $h < 363{,}725$ — in particular the exception block's height $170{,}060$ — the flags of the BIP16 exception block are `SCRIPT_VERIFY_NONE`: the exception base is empty and no height-gated rule is active.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.bip16_exception (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .bip16Block = BitcoinActivation.noFlags := by sorry
