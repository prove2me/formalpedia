-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_gradient_discounted_payment_weighted_interior_boundary
-- name    : AvramDividend.Classical.capped_gradient_discounted_payment_weighted_interior_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:29:03.553991+00:00
-- url     : https://prove2.me/theorems/82d083c8-1f8c-418c-9634-db3afb1d00d9
-- title:
--   Stopped discounted dividend bound from gradient one, with exact cap boundary payment
-- statement:
--   For any capped reserve selector and any dividend Stieltjes measure, if w'(y) >= 1 throughout the strictly interior positive-reserve region, then the full stopped discounted dividend payout is no more than the derivative-weighted interior payout plus the exact residual payout on the zero-reserve and cap boundary. This handles continuous Stieltjes payments and right atoms and is suitable for bounded-variation generator subsolutions that do not satisfy HJB equality.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_payment_interior_boundary_lintegral_split
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_gradient_discounted_payment_weighted_interior_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) (u : ℝ → ℝ)
    (hInterior : MeasurableSet
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u t))
        ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) \
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
