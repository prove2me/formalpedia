-- Prove2me | Theorems.Thm_APFPaper5_K2_keptClass_triangle_r2
-- name    : APFPaper5.K2.keptClass_triangle_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:58:21.210464+00:00
-- url     : https://prove2.me/theorems/cd7ce83c-4ff1-478b-9911-888f2e3f2bd8
-- title:
--   keptClass triangle
-- statement:
--   Scope and conditions: Recorded classes are indicators of the records kept by the true members of a supplied family. Their self-overlap equals supplied kept cost; nonnegative weights imply the record-ledger triangle inequality and exclude the stated turn table for 0<t<1. The relocated definitions and successor theorem records preserve old native versions and dependents. No statement identifies these recorded classes with a complete physical state or establishes a physical carrier.
--
--   Exact source statement:
--
--   theorem keptClass_triangle [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
--       (keeps : Finset D → W → Bool) (S T U : Finset D) :
--       recordForm w (keptClass keeps S) (keptClass keeps T) +
--           recordForm w (keptClass keeps S) (keptClass keeps U) -
--           recordForm w (keptClass keeps T) (keptClass keeps U) ≤
--         recordForm w (keptClass keeps S) (keptClass keeps S)
--
--   Source parameters:
--
--   universe uX uD uW
--   variable {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_recorded_classes:168; USB pullbacks v58 batch B; SHA-256 723174b6a77f546ff3e254cbe18930f113fce520b6db9d0ac87f426580d1edbd']

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
universe apfNative_uD apfNative_uW

theorem APFPaper5.K2.keptClass_triangle_r2 :
∀ {D : Type apfNative_uD} {W : Type apfNative_uW} [inst : Fintype.{apfNative_uW} W] (w : W → Real)
  (hw :
    ∀ (a : W),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w a))
  (keeps : Finset.{apfNative_uD} D → W → Bool) (S T U : Finset.{apfNative_uD} D),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps T))
        (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
          (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps U)))
      (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w
        (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps T)
        (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps U)))
    (@APFPaper5.K2.recordForm.{apfNative_uW} W inst w (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)
      (@APFPaper5.K2.keptClass.{apfNative_uD, apfNative_uW} D W keeps S)) := by sorry
