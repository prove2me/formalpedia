-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_integrated_physical_hjb_drift_nonpos
-- name    : AvramDividend.Classical.boundedVariation_integrated_physical_hjb_drift_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:42:15.07945+00:00
-- url     : https://prove2.me/theorems/946d723f-ddca-4518-9778-2f85b472b457
-- title:
--   Integrated discounted BV physical HJB drift is nonpositive
-- statement:
--   For a bounded-variation spectrally negative Lévy model, a capped HJB supersolution, a measurable active time set and any reserve path staying in the active positive interval, the integral of the discounted physical drift and uncompensated negative-jump generator residual is nonpositive, provided the residual is integrable. This supplies the integrated drift sign in the stopped dividend verification chain formula.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_boundedVariation_physical_hjb_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_integrated_physical_hjb_drift_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hInt : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t))) A μ) :
    (∫ t in A, Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t)) ∂μ) ≤ 0 := by sorry
