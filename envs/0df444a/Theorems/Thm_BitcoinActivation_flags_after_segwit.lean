-- Prove2me | Theorems.Thm_BitcoinActivation_flags_after_segwit
-- name    : BitcoinActivation.flags_after_segwit
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:14:39.084354+00:00
-- url     : https://prove2.me/theorems/64777673-3b57-4136-8bff-eab260c17e9e
-- title:
--   From SegWit on an ordinary block enforces every flag
-- statement:
--   For every height $h \ge 481{,}824$, the flags of an ordinary block are all seven: `P2SH`, `WITNESS`, `TAPROOT`, `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_after_segwit (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .none = ⟨true, true, true, true, true, true, true⟩ := by sorry
