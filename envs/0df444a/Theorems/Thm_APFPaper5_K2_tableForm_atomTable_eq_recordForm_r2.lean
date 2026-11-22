-- Prove2me | Theorems.Thm_APFPaper5_K2_tableForm_atomTable_eq_recordForm_r2
-- name    : APFPaper5.K2.tableForm_atomTable_eq_recordForm_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T16:05:50.046408+00:00
-- url     : https://prove2.me/theorems/803b283c-7577-43e9-8cca-758a2893503d
-- title:
--   tableForm atomTable eq recordForm
-- statement:
--   Scope and conditions: The successor retains the existing mathematical candidate results while moving three unchanged record-cost lemmas to their own source. The active indicator transforms by permutation without flips and by complementation with flips; the signed candidate transforms with signs. Supplied shared-record examples yield self-overlap four or cancellation to zero. They demonstrate limitations of these candidates and do not adopt a state representation, positive definite physical carrier, or physical hold action. Old native versions and dependents remain unchanged.
--
--   Exact source statement:
--
--   theorem tableForm_atomTable_eq_recordForm [Fintype ι] [Fintype W] (w : W → ℝ)
--       (mark : ι → W → Bool) (x y : ι → ℝ) :
--       tableForm (atomTable w mark) x y = recordForm w (markLift mark x) (markLift mark y)
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:171; USB pullbacks v58 batch B; SHA-256 431ae59f5fdcf92750d333fb33ea70e7067fe8197aab1fa0b80f8447d982d9b6']

import Definitions.Def_APFPaper5_K2_StateClass_r2
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
universe apfNative_uI apfNative_uW

theorem APFPaper5.K2.tableForm_atomTable_eq_recordForm_r2 :
∀ {ι : Type apfNative_uI} {W : Type apfNative_uW} [inst : Fintype.{apfNative_uI} ι] [inst_1 : Fintype.{apfNative_uW} W]
  (w : W → Real) (mark : ι → W → Bool) (x y : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_uI} ι inst
      (@APFPaper5.K1.atomTable.{apfNative_uI, apfNative_uW} ι W inst_1 w mark) x y)
    (@APFPaper5.K2.recordForm.{apfNative_uW} W inst_1 w
      (@APFPaper5.K2.markLift.{apfNative_uI, apfNative_uW} ι W inst mark x)
      (@APFPaper5.K2.markLift.{apfNative_uI, apfNative_uW} ι W inst mark y)) := by sorry
