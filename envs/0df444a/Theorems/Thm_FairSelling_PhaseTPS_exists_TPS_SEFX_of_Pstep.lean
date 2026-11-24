-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_exists_TPS_SEFX_of_Pstep
-- name    : FairSelling.PhaseTPS.exists_TPS_SEFX_of_Pstep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:46:55.428797+00:00
-- url     : https://prove2.me/theorems/441ded47-67d3-4448-b8b9-e561ed7eea01
-- title:
--   Phase TPS: exists TPS SEFX of Pstep
-- statement:
--   **Theorem 2 (SEFX half) reduces to the phase-structured improvement step.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L467-L488
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L467-L488

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.PhaseTPS.exists_TPS_SEFX_of_Pstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → PImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
