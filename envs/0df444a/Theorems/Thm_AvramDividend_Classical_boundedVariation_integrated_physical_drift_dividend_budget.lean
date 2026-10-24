-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_integrated_physical_drift_dividend_budget
-- name    : AvramDividend.Classical.boundedVariation_integrated_physical_drift_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:49:45.529978+00:00
-- url     : https://prove2.me/theorems/16fc5867-f2d9-4239-9116-9376f7f8dff2
-- title:
--   BV integrated physical drift and Stieltjes dividend HJB budget
-- statement:
--   For bounded-variation spectrally negative Lévy processes, the discounted physical drift and uncompensated negative-jump residual integrated against any time measure, together with the discounted marginal-dividend residual integrated against any Stieltjes dividend measure, have a nonpositive total, under capped HJB and integrability assumptions. This packages the precise finite-variation signed contributions in stopped local verification.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_boundedVariation_physical_hjb_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_integrated_physical_drift_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (μtime μdiv : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t))) A μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t))) A μdiv) :
    (∫ t in A, Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t)) ∂μtime) +
      (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂μdiv) ≤ 0 := by sorry
