-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_two_adaptive_cutoffs_same_integral
-- name    : AvramDividend.Classical.avram_p4_c_generator_two_adaptive_cutoffs_same_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:45:42.136128+00:00
-- url     : https://prove2.me/theorems/9ddd3b11-73d8-4428-8ee4-c5470678379d
-- title:
--   Exact stopped Levy physical generator drift independent of two adaptive cutoffs with L1
-- statement:
--   Two arbitrary time/state-dependent cutoff functions into (0,1), including dynamically chosen localisation mesh thresholds, yield integrable and exactly equal total discounted original physical generator residuals on any measured stopped interior region under only the source GeneratorIntegrable condition and source residual L1. Covers true original Gaussian, drift convention, negative large and compensated small jumps, including all band endpoints. No stochastic compensator or HJB sign is assumed.
-- source:
--   Source compensated generator convention, Proved adaptive cutoff transport a87a89b5-94c0-4633-b090-8687acf8646c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_adaptive_cutoff_residual_L1_transport
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_two_adaptive_cutoffs_same_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (ε δ : α → ℝ)
    (hε : ∀ p ∈ A, 0 < ε p ∧ ε p < 1)
    (hδ : ∀ p ∈ A, 0 < δ p ∧ δ p < 1)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let phys : (α → ℝ) → α → ℝ := fun r p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-(r p)), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-(r p)), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-(r p)) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn (phys ε) A μ ∧ IntegrableOn (phys δ) A μ ∧
      (∫ p in A, phys ε p ∂μ) = (∫ p in A, phys δ p ∂μ) := by sorry
