-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_integrated_generator_physical_drift_identity
-- name    : AvramDividend.Classical.boundedVariation_integrated_generator_physical_drift_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:52:34.506545+00:00
-- url     : https://prove2.me/theorems/be21ab44-ba19-4db5-a611-2ff4d0cb7817
-- title:
--   Discounted BV generator integral equals physical drift and negative jump integral
-- statement:
--   Under bounded variation and pointwise generator-integrability along a measurable active time region, the discounted integral of generator w minus q times w is equal to the discounted integral of physical drift times w-prime plus the uncompensated full negative-jump increment integral minus q times w. This is the exact expectation-level substitution needed in finite-variation stopped dividend change-of-variable calculations.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_integrated_generator_physical_drift_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hGen : ∀ t ∈ A, X.GeneratorIntegrable w (u t)) :
    (∫ t in A, Real.exp (-(q * t)) *
      (X.generator w (u t) - q * w (u t)) ∂μ) =
      ∫ t in A, Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t)) ∂μ := by sorry
