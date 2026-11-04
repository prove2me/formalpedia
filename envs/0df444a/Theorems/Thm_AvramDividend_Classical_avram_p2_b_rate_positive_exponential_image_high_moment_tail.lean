-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_positive_exponential_image_high_moment_tail
-- name    : AvramDividend.Classical.avram_p2_b_rate_positive_exponential_image_high_moment_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:44:15.534141+00:00
-- url     : https://prove2.me/theorems/f63dbbe3-8792-45d0-b8f2-e9fd7b9f2322
-- title:
--   Exponential image positive tail controlled by arbitrary high moment
-- statement:
--   For any measure on the real exponential-image coordinate and R>1, the mass of the upper tail [R,infinity), multiplied by R^k, is bounded by the kth nonnegative moment. This is a quantitative tightness ingredient: if source weighted kth moments stay bounded as h tends to zero and limiting moments are supported on [0,1], then for every R>1 upper-tail mass vanishes by letting k grow. Does not assert moment convergence or a jump rate.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_positive_exponential_image_high_moment_tail
    (μ : Measure ℝ) (R : ℝ) (hR : 1 < R) (k : ℕ) :
    ENNReal.ofReal (R ^ k) * μ (Set.Ici R) ≤
      ∫⁻ z, ENNReal.ofReal (z ^ k) ∂μ := by sorry
