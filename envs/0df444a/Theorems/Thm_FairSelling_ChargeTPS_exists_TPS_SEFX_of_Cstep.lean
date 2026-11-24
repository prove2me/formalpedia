-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_exists_TPS_SEFX_of_Cstep
-- name    : FairSelling.ChargeTPS.exists_TPS_SEFX_of_Cstep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:15.7606+00:00
-- url     : https://prove2.me/theorems/38730e4b-167a-4796-ac71-3765b18b5cbd
-- title:
--   Charge TPS: exists TPS SEFX of Cstep
-- statement:
--   **Theorem 2 (SEFX half) reduces to the charged improvement step.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L450-L464
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L450-L464

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.ChargeTPS.exists_TPS_SEFX_of_Cstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → CImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
