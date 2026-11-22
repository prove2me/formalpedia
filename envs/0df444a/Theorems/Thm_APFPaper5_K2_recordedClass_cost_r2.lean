-- Prove2me | Theorems.Thm_APFPaper5_K2_recordedClass_cost_r2
-- name    : APFPaper5.K2.recordedClass_cost_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T16:01:49.772887+00:00
-- url     : https://prove2.me/theorems/e33a4d0a-872e-4c4b-be8c-e1183f79f771
-- title:
--   recordedClass cost
-- statement:
--   Scope and conditions: Recorded classes are indicators of the records kept by the true members of a supplied family. Their self-overlap equals supplied kept cost; nonnegative weights imply the record-ledger triangle inequality and exclude the stated turn table for 0<t<1. The relocated definitions and successor theorem records preserve old native versions and dependents. No statement identifies these recorded classes with a complete physical state or establishes a physical carrier.
--
--   Exact source statement:
--
--   theorem recordedClass_cost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool)
--       (reads : D → X → Bool) (S : Finset D) (x : X) :
--       recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S x) =
--         keptCost w keeps (heldFamily reads S x)
--
--   Source parameters:
--
--   universe uX uD uW
--   variable {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_recorded_classes:161; USB pullbacks v58 batch B; SHA-256 723174b6a77f546ff3e254cbe18930f113fce520b6db9d0ac87f426580d1edbd']

import Definitions.Def_APFPaper5_K2_RecordedClass
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_triangle
import Theorems.Thm_APFPaper5_K1_atomTable_le_diag
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_triangle
import Theorems.Thm_APFPaper5_K1_turnTable_symm
import Theorems.Thm_APFPaper5_K1_turnTable_breaks_triangle
import Theorems.Thm_APFPaper5_K1_no_record_ledger_has_turnTable
import Theorems.Thm_APFPaper5_K1_no_three_distinctions_have_turnTable
import Theorems.Thm_APFPaper5_K1_turnTable_half_form
import Theorems.Thm_APFPaper5_K1_turnTable_half_nonneg
import Theorems.Thm_APFPaper5_K1_turnTable_half_faithful
import Theorems.Thm_APFPaper5_K1_ownTable_eq
import Theorems.Thm_APFPaper5_K1_turnClass_negative
import Theorems.Thm_APFPaper5_K1_turnTable_on_classes
set_option autoImplicit false
universe apfNative_uX apfNative_uD apfNative_uW

theorem APFPaper5.K2.recordedClass_cost_r2 :
∀ {X : Type apfNative_uX} {D : Type apfNative_uD} {W : Type apfNative_uW} [inst : Fintype.{apfNative_uW} W]
  (w : W → Real) (keeps : Finset.{apfNative_uD} D → W → Bool) (reads : D → X → Bool) (S : Finset.{apfNative_uD} D)
  (x : X),
  @Eq.{1} Real
    (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
      (@APFPaper5.K2.recordedClass.{apfNative_uX, apfNative_uD, apfNative_uW} X D W keeps reads S x)
      (@APFPaper5.K2.recordedClass.{apfNative_uX, apfNative_uD, apfNative_uW} X D W keeps reads S x))
    (@APFPaper5.K1.keptCost.{apfNative_uD, apfNative_uW} D W inst w keeps
      (@APFPaper5.K2.heldFamily.{apfNative_uX, apfNative_uD} X D reads S x)) := by sorry
