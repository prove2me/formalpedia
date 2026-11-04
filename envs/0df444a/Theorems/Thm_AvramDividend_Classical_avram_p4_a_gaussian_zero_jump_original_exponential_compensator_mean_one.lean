-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_exponential_compensator_mean_one
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_exponential_compensator_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:58:14.714202+00:00
-- url     : https://prove2.me/theorems/e6b5b001-d96a-4204-abc8-6f1509c141be
-- title:
--   Original zero-jump Levy Gaussian-centred compensated exponential has unit expectation
-- statement:
--   The original source zero-jump Levy component has a positive Gaussian-compensated centred exponential with expectation one at each deterministic time, from the already proved positive Laplace identity. This is the unconditional normalisation prerequisite for its exponential martingale and does not assert conditional independence or a Brownian integral.
-- source:
--   Original SpectrallyNegativeLevy source Laplace triplet and Proved centred Laplace theorem, Avram Palmowski Pistorius section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_exponential_compensator_mean_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
       (θ * (Y.X t ω - (t : ℝ) * Y.c) -
         (t : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) ∂P) = 1 := by sorry
