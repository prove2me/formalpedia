-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_laplace_exponent_quadratic
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_laplace_exponent_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:15:49.940202+00:00
-- url     : https://prove2.me/theorems/00621cf4-ab20-4263-8ea3-cdadc0b41144
-- title:
--   Original Levy zero-jump Laplace exponent reduces to Gaussian quadratic form
-- statement:
--   For any actual spectrally negative Levy process in the source filtered probability-space structure whose Levy jump measure is zero, the source Laplace exponent is identically c theta plus half sigma squared theta squared. This is the original generator convention and does not add a Brownian random process.
-- source:
--   Source definition AvramDividend_Classical_SpectrallyNegativeLevy, laplaceExponent and SpectrallyNegativeLevy.psi; Avram Palmowski Pistorius section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_laplace_exponent_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (θ : ℝ) :
    Y.ψ θ = Y.c * θ + Y.σ ^ 2 * θ ^ 2 / 2 := by sorry
