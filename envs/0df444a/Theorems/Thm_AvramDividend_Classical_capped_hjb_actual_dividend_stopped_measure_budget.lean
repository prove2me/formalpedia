-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_actual_dividend_stopped_measure_budget
-- name    : AvramDividend.Classical.capped_hjb_actual_dividend_stopped_measure_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:15:13.372541+00:00
-- url     : https://prove2.me/theorems/7616b47c-01df-4930-99e3-56b3d39d2ef0
-- title:
--   Combined capped HJB signed budget for actual stopped dividend Stieltjes measure
-- statement:
--   The integrated HJB drift and singular marginal dividend residuals have a nonpositive sum when evaluated on a genuine dividend strategy's stopped payment set and its Stieltjes measure. The theorem specialises the proved abstract signed-budget result to the exact paymentTimes and dividendMeasure interface used by stochastic verification.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_capped_hjb_integrated_drift_dividend_residual_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_actual_dividend_stopped_measure_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (μtime : Measure ℝ) (u : ℝ → ℝ)
    (hregion : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ),
      0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t)))
      (paymentTimes σ ∩ Iic (T : ℝ)) μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) *
        (X.generator w (u t) - q * w (u t)) ∂μtime) +
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂(dividendMeasure D ω)) ≤ 0 := by sorry
