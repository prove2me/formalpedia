-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_physical_cutoff_independent_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_physical_cutoff_independent_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:38:58.515718+00:00
-- url     : https://prove2.me/theorems/310ae99c-5c0c-4529-95e5-9057f5a03143
-- title:
--   Unconditional source generator weighted L1 transports to cutoff-independent stopped physical drift
-- statement:
--   Under the original spectrally negative Levy source generator-domain condition and an actual L1 source residual on any measured stopped region, two arbitrary truncation conventions epsilon and delta yield independently integrable original discounted physical Gaussian, renormalised drift, raw-large, compensated-small residuals, whose stopped integrals agree. No sign/HJB condition or compensator identity is assumed.
-- source:
--   Proved source L1 transport 6e1fd58b-f74d-414a-959b-d75d88923587, exact physical generator cutoff convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_physical_residual_L1_transport
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_physical_cutoff_independent_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (μ : Measure α) (clock u : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C) :
    let F : α → ℝ := fun p => Real.exp (-(q * clock p)) *
      (X.generator w (u p) - q * w (u p))
    let phys : ℝ → α → ℝ := fun r p => Real.exp (-(q * clock p)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-r), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-r), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-r) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn (phys ε) A μ ∧ IntegrableOn (phys δ) A μ ∧
      (∫ p in A, phys ε p ∂μ) = (∫ p in A, phys δ p ∂μ) := by sorry
