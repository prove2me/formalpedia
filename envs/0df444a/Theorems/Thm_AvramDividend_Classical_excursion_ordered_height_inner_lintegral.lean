-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_ordered_height_inner_lintegral
-- name    : AvramDividend.Classical.excursion_ordered_height_inner_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:01:32.625077+00:00
-- url     : https://prove2.me/theorems/6b01d267-79ab-43d8-8541-b41b28369ec5
-- title:
--   Ordered-region height integral equals the positive truncated-height interval integral
-- statement:
--   For each fixed jump size z, the ordered region 0<t<z is the measurable interval Ioo 0 z. Therefore the Tonelli inner height integral equals the constant jump weight g times the interval integral of w. This handles even z≤0, for which both sides vanish. It is the right-side identification for the positive descending ladder kernel.
-- source:
--   Pinned MeasureTheory.lintegral_indicator, lintegral_const_mul, lintegral_mul_const and set indicator simplification.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.excursion_ordered_height_inner_lintegral
    (z : ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (g : ℝ≥0∞) :
    (∫⁻ t : ℝ, (if 0 < t ∧ t < z then w t * g else 0) ∂volume) =
      g * (∫⁻ t in Ioo (0 : ℝ) z, w t ∂volume) := by sorry
