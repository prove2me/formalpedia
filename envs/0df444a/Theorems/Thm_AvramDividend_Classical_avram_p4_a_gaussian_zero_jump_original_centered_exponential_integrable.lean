-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:30:34.726476+00:00
-- url     : https://prove2.me/theorems/ea52d27e-5c59-4d5a-887c-8e26b28498af
-- title:
--   Original zero-jump Levy centred positive exponential integrability
-- statement:
--   For a zero-jump spectrally negative Levy process in the original source model, every positive exponential moment of the drift-centred process at deterministic time is finite. It uses the source Laplace-integrability field, without assuming Brownian motion or stochastic integration.
-- source:
--   Original SpectrallyNegativeLevy.laplace field, Avram Palmowski Pistorius section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c))) P := by sorry
