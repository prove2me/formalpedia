-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_stopped_cutoff_independent
-- name    : AvramDividend.Classical.avram_p4_c_generator_weighted_stopped_cutoff_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:35:35.164199+00:00
-- url     : https://prove2.me/theorems/1f279cf1-20af-41ec-9b4a-be7e78bfe4c9
-- title:
--   Cutoff-independent original discounted stopped generator integrals with automatic L1 and HJB sign
-- statement:
--   At any strict interior measured stopped region, the exact original Gaussian/renormalised-drift/uncompensated-large/compensated-small generator residual has an integrable discounted density for two arbitrary 0<epsilon,delta<1 cutoffs whenever the source weighted generator residual is L1. Both physical integrals equal that source residual and are therefore cutoff independent and nonpositive under the original HJB. No stochastic compensator is asserted.
-- source:
--   Source exact epsilon generator identity and Proved P4-C weighted physical L1/sign f9d4f8ff-0c2b-4bc3-a151-55ab330f1469.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_physical_L1_and_sign
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_weighted_stopped_cutoff_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {α : Type*} [mα : MeasurableSpace α]
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (μ : Measure α) (u a : α → ℝ) (A : Set α)
    (hA : MeasurableSet A)
    (hregion : ∀ p ∈ A, 0 < u p ∧ ENNReal.ofReal (u p) < C)
    (ha : ∀ p ∈ A, 0 ≤ a p) :
    let F : α → ℝ := fun p =>
      a p * (X.generator w (u p) - q * w (u p))
    let phys : ℝ → α → ℝ := fun r p => a p *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (u p) +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-r), z ∂X.ν)) * deriv w (u p) +
        (∫ z in Iio (-r), w (u p + z) - w (u p) ∂X.ν) +
        (∫ z in Ico (-r) 0,
          SpectrallyNegativeLevy.generatorIntegrand w (u p) z ∂X.ν) -
        q * w (u p))
    IntegrableOn F A μ →
      IntegrableOn (phys ε) A μ ∧ IntegrableOn (phys δ) A μ ∧
      (∫ p in A, phys ε p ∂μ) = (∫ p in A, phys δ p ∂μ) ∧
      (∫ p in A, phys ε p ∂μ) ≤ 0 := by sorry
