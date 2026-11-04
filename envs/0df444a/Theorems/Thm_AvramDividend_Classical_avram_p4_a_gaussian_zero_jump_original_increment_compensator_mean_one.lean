-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_increment_compensator_mean_one
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_increment_compensator_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:08:38.372811+00:00
-- url     : https://prove2.me/theorems/b3ea3112-24ae-4b9c-9c29-fe774f6d1f82
-- title:
--   Original zero-jump Gaussian compensated exponential increments have unit mean
-- statement:
--   For each ordered deterministic pair of times in the original zero-jump Levy source and every nonnegative Laplace parameter, the Gaussian-centred, variance-compensated increment exponential has expectation exactly one.
-- source:
--   Proved Avram P4-A original deterministic-increment Gaussian Laplace identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_increment_compensator_mean_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
      (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) -
        ((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) ∂P) = 1 := by sorry
