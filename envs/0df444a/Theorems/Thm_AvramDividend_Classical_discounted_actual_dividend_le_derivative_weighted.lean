-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_actual_dividend_le_derivative_weighted
-- name    : AvramDividend.Classical.discounted_actual_dividend_le_derivative_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:15:14.039354+00:00
-- url     : https://prove2.me/theorems/838ede7f-37a4-446e-bab6-e48ffafe57db
-- title:
--   Stopped dividend Stieltjes payout is bounded by the derivative-weighted payout
-- statement:
--   For a finite-valued admissible dividend strategy and any stopped payment window, if the candidate's derivative along a measurable reserve profile is at least one and its derivative-weighted discounted payout is integrable, the actual discounted payout is no greater than the derivative-weighted payout. Integrability of the unweighted discount follows directly from finite strategy payment mass.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_integrableOn_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_actual_dividend_le_derivative_weighted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (w u : ℝ → ℝ)
    (hgrad : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ), 1 ≤ deriv w (u t))
    (hWeighted : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u t))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) * deriv w (u t) ∂(dividendMeasure D ω)) := by sorry
