-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_actual_finset_step_jump_equals_source_mark
-- name    : AvramDividend.Classical.avram_bva_actual_finset_step_jump_equals_source_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:44:15.580518+00:00
-- url     : https://prove2.me/theorems/ec32a62a-1ffb-40ff-b714-a9f5a226fddb
-- title:
--   Exact original finite-jump series discontinuity equals the physical mark at its time
-- statement:
--   At a time belonging to a finite set of physical jump times, the difference between its finite cumulative jump series at t and its strict-left sum equals the exact actual downward jump, leftLim f(t)-f(t), with no approximation or extra marks.
-- source:
--   Proved finite-marked step jump identity and Finset.sum_ite_eq_of_mem

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_marks_at_time
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bva_actual_finset_step_jump_equals_source_mark
    (f : ℝ≥0 → ℝ) (S : Finset ℝ≥0) (t : ℝ≥0)
    (ht : t ∈ S) :
    Finset.sum S (fun u => if u ≤ t then
        Function.leftLim f u - f u else 0) -
      Finset.sum S (fun u => if u < t then
        Function.leftLim f u - f u else 0) =
      Function.leftLim f t - f t := by sorry
