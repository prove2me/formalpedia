-- Prove2me | Theorems.Thm_BitcoinActivation_activeAt_mono
-- name    : BitcoinActivation.activeAt_mono
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:14:11.043825+00:00
-- url     : https://prove2.me/theorems/21f96033-17e8-4f85-8eb6-119f8c27d1c3
-- title:
--   Buried-deployment activation is monotone in height
-- statement:
--   For every buried deployment and heights $h_1 \le h_2$, if the deployment is active at $h_1$ then it is active at $h_2$: a buried deployment, once active, stays active.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.activeAt_mono (dep : BuriedDeployment) (h₁ h₂ : Nat) (h : h₁ ≤ h₂)
    (ha : BitcoinActivation.activeAt h₁ dep = true) : BitcoinActivation.activeAt h₂ dep = true := by sorry
