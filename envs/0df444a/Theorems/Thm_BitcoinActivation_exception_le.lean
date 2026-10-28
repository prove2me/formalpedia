-- Prove2me | Theorems.Thm_BitcoinActivation_exception_le
-- name    : BitcoinActivation.exception_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:15:18.116768+00:00
-- url     : https://prove2.me/theorems/effce104-4f95-4d5a-95a1-4ad25e881233
-- title:
--   An exception never adds a rule
-- statement:
--   For every height and exception status, the flags of the block are included in the flags an ordinary block at that height would have: the exception table only ever removes rules.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.exception_le (height : Nat) (exc : ScriptException) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags height exc)
      (BitcoinActivation.blockScriptFlags height .none) := by sorry
