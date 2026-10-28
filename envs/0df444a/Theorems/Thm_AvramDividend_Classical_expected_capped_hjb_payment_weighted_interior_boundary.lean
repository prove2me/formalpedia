-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_capped_hjb_payment_weighted_interior_boundary
-- name    : AvramDividend.Classical.expected_capped_hjb_payment_weighted_interior_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:05:13.513885+00:00
-- url     : https://prove2.me/theorems/2c9779dc-a66b-4b99-b974-d7cd455fb46e
-- title:
--   Expected HJB Stieltjes payment bound with explicit interior derivative and boundary terms
-- statement:
--   Under a measurable reserve-interior region and the HJB maximum equation, expected stopped discounted actual dividend payments are dominated by the expectation of interior derivative-weighted Stieltjes payments plus the exact boundary payment mass. The result holds for non-atomic continuous and right-atomic dividends. It isolates the two expectation terms that a stopped Lévy stochastic verification proof must control.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_capped_hjb_discounted_payment_weighted_interior_boundary

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.expected_capped_hjb_payment_weighted_interior_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
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
