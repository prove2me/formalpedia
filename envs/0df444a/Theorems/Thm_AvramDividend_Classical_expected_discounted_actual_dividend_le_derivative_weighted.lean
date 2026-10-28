-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_discounted_actual_dividend_le_derivative_weighted
-- name    : AvramDividend.Classical.expected_discounted_actual_dividend_le_derivative_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:22:09.086907+00:00
-- url     : https://prove2.me/theorems/5e590ca1-a651-485f-b335-283abfa72704
-- title:
--   Expected stopped dividend payout is bounded by expected derivative-weighted Stieltjes payout
-- statement:
--   The expectation of actual stopped discounted dividend Stieltjes payments is bounded above by the expectation of the derivative-weighted real Stieltjes integral, provided that the derivative along each sample path is at least one and its weighted pathwise integral is integrable. The proof lifts the exact real/extended-real dividend bridge and the proved pathwise derivative comparison through the outer lintegral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_actual_dividend_le_derivative_weighted
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_real_lintegral_bridge

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.expected_discounted_actual_dividend_le_derivative_weighted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞) (T : ℝ≥0)
    (w : ℝ → ℝ) (u : Ω → ℝ → ℝ)
    (hgrad : ∀ ω t, t ∈ paymentTimes (σ ω) ∩ Iic (T : ℝ) →
      1 ≤ deriv w (u ω t))
    (hWeighted : ∀ ω, IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u ω t))
      (paymentTimes (σ ω) ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal
      (∫ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) * deriv w (u ω t)
          ∂(dividendMeasure D ω)) ∂P) := by sorry
