-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
-- name    : AvramDividend.Classical.avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:45:46.352092+00:00
-- url     : https://prove2.me/theorems/baf85154-fdb5-4f40-b870-7ea42f6af7e9
-- title:
--   Original nonlinear marked-count jump kernel integral is its time-indexed jump tsum
-- statement:
--   The integral of any measurable nonnegative nonlinear jump kernel against the actual marked-count measure of a measurable jump-time support is exactly the time-indexed sum of the kernel evaluated at the original time-marks. Applies to nonlinear HJB jump source after separately proving the original time-mark map is measurable; no replacement Poisson measure or finite-activity assumption.
-- source:
--   Pinned Mathlib lintegral_map, lintegral_indicator and lintegral_count, directly applied to the original marked count representation appearing in E2 and the canonical P3 proof.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Count

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

/-- Exact marked-count integral of a nonlinear nonnegative jump kernel,
with a genuinely measurable original time-mark map. -/

theorem AvramDividend.Classical.avram_p3_2_original_marked_count_nonlinear_lintegral_eq_tsum
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    (mark : ℝ≥0 → ℝ≥0 × ℝ) (hmark : Measurable mark)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂((Measure.count.restrict S).map mark)) =
      ∑' u : ℝ≥0, if u ∈ S then F (mark u) else 0 := by sorry
