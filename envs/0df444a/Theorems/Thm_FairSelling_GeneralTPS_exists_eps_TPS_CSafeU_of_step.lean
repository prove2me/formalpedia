-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_exists_eps_TPS_CSafeU_of_step
-- name    : FairSelling.GeneralTPS.exists_eps_TPS_CSafeU_of_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:47.289289+00:00
-- url     : https://prove2.me/theorems/be7a86be-02fc-4411-a56e-bb846db02882
-- title:
--   General TPS: exists eps TPS CSafe U of step
-- statement:
--   **Theorem 2 (SEFX half) reduces to the improvement step**, in its `ε`-approximate form.  If
--   the improvement step of the manuscript's Algorithm 6 can always be performed, then for every
--   `ε > 0` there is a conceptual assignment which gives every agent its threshold and in which no
--   agent `ε`-SEFX-envies another.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L372-L389
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L372-L389

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.GeneralTPS.exists_eps_TPS_CSafeU_of_step (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, CSafeU v p eps A q i j) := by sorry
