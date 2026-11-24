-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_exists_eps_TPS_CSafeU_of_Cstep
-- name    : FairSelling.ChargeTPS.exists_eps_TPS_CSafeU_of_Cstep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:20.381997+00:00
-- url     : https://prove2.me/theorems/77d0e258-88c6-455c-af39-3a034dff794f
-- title:
--   Charge TPS: exists eps TPS CSafe U of Cstep
-- statement:
--   The `ε`-approximate form of Theorem 2 (SEFX half), from the charged improvement step.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L428-L447
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L428-L447

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

theorem FairSelling.ChargeTPS.exists_eps_TPS_CSafeU_of_Cstep (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (eps : ℝ) (heps : 0 < eps) (hstep : CImprovementStep v p eps) :
    ∃ (A : Fin n → Finset G) (F : Finset G) (q : Fin n → ℝ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, Disjoint F (A i)) ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i ≤ ∑ g ∈ F, p g) ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ vbarSum (v i) p (A i) + q i) ∧
      (∀ i j, GeneralTPS.CSafeU v p eps A q i j) := by sorry
