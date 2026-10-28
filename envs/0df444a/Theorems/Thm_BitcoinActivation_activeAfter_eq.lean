-- Prove2me | Theorems.Thm_BitcoinActivation_activeAfter_eq
-- name    : BitcoinActivation.activeAfter_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:14:20.973576+00:00
-- url     : https://prove2.me/theorems/47d978e6-f401-4b48-9407-e62c2a1490a1
-- title:
--   Active-after is active-at the next height
-- statement:
--   For every buried deployment and previous height $p$, `activeAfter`$(p, dep)$ equals `activeAt`$(p+1, dep)$: `DeploymentActiveAfter(pindexPrev)` is `DeploymentActiveAt` of the block that follows.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.activeAfter_eq (dep : BuriedDeployment) (prevHeight : Nat) :
    BitcoinActivation.activeAfter prevHeight dep = BitcoinActivation.activeAt (prevHeight + 1) dep := by sorry
