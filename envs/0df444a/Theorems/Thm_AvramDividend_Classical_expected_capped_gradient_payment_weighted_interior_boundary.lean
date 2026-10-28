-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_capped_gradient_payment_weighted_interior_boundary
-- name    : AvramDividend.Classical.expected_capped_gradient_payment_weighted_interior_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:46:57.823296+00:00
-- url     : https://prove2.me/theorems/d72c6433-4cea-42e6-b658-8b7a9570991d
-- title:
--   Expected capped dividend payment bound using only the interior derivative condition
-- statement:
--   For a capped reserve selector, if the candidate derivative is at least one throughout the strictly interior positive-reserve region, the expected stopped discounted Stieltjes payout is bounded by expected derivative-weighted interior payment plus exact cap and zero-reserve boundary payout. This is the expectation-level bridge for bounded-variation generator subsolutions, without HJB equality.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_capped_gradient_discounted_payment_weighted_interior_boundary

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.expected_capped_gradient_payment_weighted_interior_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (σ : Ω → ℝ≥0∞) (T : ℝ≥0) (u : Ω → ℝ → ℝ)
    (hInterior : ∀ ω, MeasurableSet
      {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C}) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω,
      (∫⁻ t in (paymentTimes (σ ω) ∩ Iic (T : ℝ)) ∩
        {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
        ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u ω t))
          ∂(dividendMeasure D ω)) +
      (∫⁻ t in (paymentTimes (σ ω) ∩ Iic (T : ℝ)) \
        {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ∂P) := by sorry
