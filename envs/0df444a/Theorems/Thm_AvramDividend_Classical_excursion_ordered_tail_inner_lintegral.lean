-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_ordered_tail_inner_lintegral
-- name    : AvramDividend.Classical.excursion_ordered_tail_inner_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:01:30.49956+00:00
-- url     : https://prove2.me/theorems/ecf58816-2516-4c4d-a165-de248a9c358a
-- title:
--   Ordered-region jump integral equals the positive weighted jump tail
-- statement:
--   For positive height threshold t, an ordered pair 0<t<z is equivalent to z∈Ioi t. Thus the inner Tonelli integral of w*g(z) over 0<t<z equals the constant w multiplied by the tail integral of g above t. This is the left-side identification for the positive descending ladder kernel.
-- source:
--   Pinned MeasureTheory.lintegral_indicator, lintegral_const_mul, lintegral_mul_const and set indicator simplification.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.excursion_ordered_tail_inner_lintegral
    (μ : Measure ℝ) (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) (w : ℝ≥0∞) :
    (∫⁻ z : ℝ, (if 0 < t ∧ t < z then w * g z else 0) ∂μ) =
      w * (∫⁻ z in Ioi t, g z ∂μ) := by sorry
