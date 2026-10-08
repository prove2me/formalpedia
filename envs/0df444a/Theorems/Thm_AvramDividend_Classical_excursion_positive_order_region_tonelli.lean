-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_positive_order_region_tonelli
-- name    : AvramDividend.Classical.excursion_positive_order_region_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:57:43.767212+00:00
-- url     : https://prove2.me/theorems/75f02556-2d27-476b-840d-60fd00d98d93
-- title:
--   Tonelli exchange over the positive ordered jump-height region
-- statement:
--   For any sigma-finite positive-jump measure μ and measurable nonnegative weights w(t), g(z), Tonelli permits swapping integration in the region 0<t<z. The integrand is the product w(t)g(z) there and zero elsewhere. In the ladder-height construction, w(t)=min(1,t) and g(z)=exp(-φz), so the identity exchanges the integral over height thresholds of the jump-tail kernel with an integral over original jump magnitudes of the truncated height area. This theorem isolates only the measure-theoretic Fubini/Tonelli part, without invoking a stochastic excursion process.
-- source:
--   Pinned MeasureTheory.lintegral_lintegral_swap, Measurable.ite and measurableSet_lt; product Lebesgue and Lévy measures.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.excursion_positive_order_region_tonelli
    (μ : Measure ℝ) [SFinite μ]
    (w g : ℝ → ℝ≥0∞) (hw : Measurable w) (hg : Measurable g) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then w t * g z else 0) ∂μ ∂volume) =
    (∫⁻ z : ℝ, ∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then w t * g z else 0) ∂volume ∂μ) := by sorry
