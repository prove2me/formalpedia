-- Prove2me | Theorems.Thm_BitcoinActivation_taproot_exception
-- name    : BitcoinActivation.taproot_exception
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:15:05.891009+00:00
-- url     : https://prove2.me/theorems/2aafc6d4-d0ea-4352-82f4-529a3b6686eb
-- title:
--   The Taproot exception block enforces every flag except Taproot
-- statement:
--   For every height $h \ge 481{,}824$ — in particular the exception block's height $692{,}261$ — the flags of the Taproot exception block are `P2SH | WITNESS | DERSIG | CHECKLOCKTIMEVERIFY | CHECKSEQUENCEVERIFY | NULLDUMMY`: the exception removes `TAPROOT` only, and the height-gated rules are all active.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.taproot_exception (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .taprootBlock = ⟨true, true, false, true, true, true, true⟩ := by sorry
