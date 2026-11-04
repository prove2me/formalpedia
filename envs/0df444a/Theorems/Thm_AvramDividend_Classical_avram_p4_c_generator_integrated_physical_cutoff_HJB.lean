-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_integrated_physical_cutoff_HJB
-- name    : AvramDividend.Classical.avram_p4_c_generator_integrated_physical_cutoff_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:03:48.378883+00:00
-- url     : https://prove2.me/theorems/59dd858d-36a6-4d00-b6c2-c9d26223bc92
-- title:
--   Nonpositive integrated discounted original physical generator residual on measurable interior localisation
-- statement:
--   For any time measure μ, measurable region A, reserve path u constrained strictly to 0<u(t)<C on A, 0<epsilon<1 and original source HJB/GeneratorIntegrable, the discounted physical ε-renormalised generator residual integrates to a nonpositive value whenever the assembled residual is integrable on A. This uses exact source generator identity and exp positivity; the integrability premise is explicit and no stochastic path or finite-variation decomposition is assumed.
-- source:
--   P4-C original_epsilon_drift_compact; Mathlib integral_nonpos_of_ae and ae_restrict_mem

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_integrated_physical_cutoff_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C) :
    let G : ℝ → ℝ := fun t =>
      Real.exp (-(q * t)) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u t) +
          (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w (u t) +
          (∫ z in Iio (-ε), w (u t + z) - w (u t) ∂X.ν) +
          (∫ z in Ico (-ε) 0,
            SpectrallyNegativeLevy.generatorIntegrand w (u t) z ∂X.ν) -
          q * w (u t))
    IntegrableOn G A μ → (∫ t in A, G t ∂μ) ≤ 0 := by sorry
