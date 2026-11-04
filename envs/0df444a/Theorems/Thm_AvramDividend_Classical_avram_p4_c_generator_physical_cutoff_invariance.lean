-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_physical_cutoff_invariance
-- name    : AvramDividend.Classical.avram_p4_c_generator_physical_cutoff_invariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:58:31.675295+00:00
-- url     : https://prove2.me/theorems/84f924da-3ccb-4d00-ba1f-2a28cb796946
-- title:
--   Original physical-generator Gaussian, epsilon drift and all jump integrals are invariant under two strict cutoffs
-- statement:
--   Under original GeneratorIntegrable, the fully assembled physical Gaussian-plus-renormalised-drift-plus-large-raw-and-small-compensated generator is independent of the arbitrary 0<epsilon<1 cutoff. Two choices epsilon and delta are equal by their separately proven identification with the exact source X.generator. No uniform epsilon limit or stochastic compensation is claimed.
-- source:
--   P4-C original_epsilon_drift_identification

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_physical_cutoff_invariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgen : X.GeneratorIntegrable w y) :
    let F : ℝ → ℝ := fun η =>
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-η), z ∂X.ν)) * deriv w y +
        (∫ z in Iic (-1 : ℝ), w (y + z) - w y ∂X.ν) +
        (∫ z in Ioo (-1 : ℝ) (-η), w (y + z) - w y ∂X.ν) +
        (∫ z in Ico (-η) 0,
          SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν)
    F ε = F δ := by sorry
