-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_candidate_strict_interior_C1
-- name    : AvramDividend.Classical.avram_bvb_obstruction_half_affine_candidate_strict_interior_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:00:43.009398+00:00
-- url     : https://prove2.me/theorems/0a39d2f4-3418-4223-8abd-86ffdbcaee0e
-- title:
--   Half-unit affine dividend verification candidate is C1 on every strictly positive cap interior
-- statement:
--   For every dividend cap C, the piecewise positive-affine candidate w(y)=0 for y<0 and 1/2+y otherwise is C1 on all strictly positive reserve points below the cap. This supplies the exact original BV candidate regularity hypothesis, allowing a jump at zero.
-- source:
--   On the strict interior {y|0<y∧ofReal(y)<C}, the function equals the globally smooth affine map y↦1/2+y. Apply ContDiffOn.congr to an affine ContDiff proof.

import Mathlib
open MeasureTheory Set Real
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_half_affine_candidate_strict_interior_C1 (C : ℝ≥0∞) :
    ContDiffOn ℝ 1 (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
