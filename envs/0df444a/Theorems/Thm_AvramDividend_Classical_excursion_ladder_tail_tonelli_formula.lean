-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_ladder_tail_tonelli_formula
-- name    : AvramDividend.Classical.excursion_ladder_tail_tonelli_formula
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T08:09:31.815577+00:00
-- url     : https://prove2.me/theorems/b271c37b-8452-4f28-9d45-a842c201640e
-- title:
--   Positive ladder-height weighted tail integral equals weighted truncated jump-height area
-- statement:
--   The positive-threshold weighted jump-tail integral is equal to the integral over jump magnitudes of the weighted truncated height area. Apply Tonelli on the ordered region 0<t<z and identify the nested integrals via indicator identities. Specialising to min(1,t) and the Esscher exponential yields the exact first-moment identity for the descending ladder-height Lévy measure.
-- source:
--   excursion_positive_order_region_tonelli; excursion_ordered_tail_inner_lintegral; excursion_ordered_height_inner_lintegral.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.excursion_ladder_tail_tonelli_formula
    (μ : Measure ℝ) [SFinite μ]
    (w g : ℝ → ℝ≥0∞) (hw : Measurable w) (hg : Measurable g) :
    (∫⁻ t : ℝ, (Ioi (0 : ℝ)).indicator w t *
       (∫⁻ z in Ioi t, g z ∂μ) ∂volume) =
    (∫⁻ z : ℝ, g z *
       (∫⁻ t in Ioo (0 : ℝ) z, w t ∂volume) ∂μ) := by sorry
