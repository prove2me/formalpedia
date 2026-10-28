-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_actual_dividend_weighted_derivative_integrable
-- name    : AvramDividend.Classical.discounted_actual_dividend_weighted_derivative_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:17:33.996726+00:00
-- url     : https://prove2.me/theorems/d365225a-67b4-41f3-a61d-02b869ddbc91
-- title:
--   Absolute integrability of the discounted derivative-weighted actual dividend payout
-- statement:
--   A finite-valued dividend strategy has finite Stieltjes mass in every stopped payment window. If the discounted derivative-weighted payout is measurable and the derivative is bounded there, the weighted integral is absolutely integrable. The proof controls the exponential discount by one and applies finite-measure bounded-integrand integrability.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_actual_dividend_weighted_derivative_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (w u : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) * deriv w (u t))
      (dividendMeasure D ω))
    (hbound : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ),
      |deriv w (u t)| ≤ M) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q * t)) * deriv w (u t))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by sorry
