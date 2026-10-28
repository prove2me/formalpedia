-- Prove2me | Theorems.Thm_BitcoinActivation_lockTimeFlags_eq
-- name    : BitcoinActivation.lockTimeFlags_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:15:28.581837+00:00
-- url     : https://prove2.me/theorems/158103f1-2a50-47ad-b807-eebdb9d07ccf
-- title:
--   Sequence locks are verified exactly from CSV activation
-- statement:
--   For every height $h$, `lockTimeFlags`$(h)$ is `LOCKTIME_VERIFY_SEQUENCE` when $419{,}328 \le h$ and $0$ otherwise: BIP68 relative locks are enforced from the CSV activation height on.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.lockTimeFlags_eq (height : Nat) :
    BitcoinActivation.lockTimeFlags height =
      if 419328 ≤ height then BitcoinActivation.LOCKTIME_VERIFY_SEQUENCE else 0 := by sorry
