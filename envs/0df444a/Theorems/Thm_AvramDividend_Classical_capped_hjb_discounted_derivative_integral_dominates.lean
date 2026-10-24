-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_hjb_discounted_derivative_integral_dominates
-- name    : AvramDividend.Classical.capped_hjb_discounted_derivative_integral_dominates
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:42:56.461666+00:00
-- url     : https://prove2.me/theorems/ff302cd7-b7f5-4d3e-af36-e275343ed6fa
-- title:
--   Capped HJB derivative dominates discounted dividend measure
-- statement:
--   For any measure on time, possibly atom-bearing or singular, the discounted integral of the measure over a measurable active region is bounded above by the discounted integral weighted by the derivative of any capped HJB supersolution. This follows from w' >= 1 and positivity of exponential discount; with explicit integrability assumptions it is suitable for Stieltjes dividend estimates in both bounded and unbounded variation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_hjb_discounted_derivative_integral_dominates
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hExp : IntegrableOn (fun t : ℝ => Real.exp (-(q * t))) A μ)
    (hDer : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u t)) A μ) :
    (∫ t in A, Real.exp (-(q * t)) ∂μ) ≤
      ∫ t in A, Real.exp (-(q * t)) * deriv w (u t) ∂μ := by sorry
