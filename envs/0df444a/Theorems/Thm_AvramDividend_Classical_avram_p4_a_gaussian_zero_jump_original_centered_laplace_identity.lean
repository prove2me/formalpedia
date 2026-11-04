-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:17:23.910467+00:00
-- url     : https://prove2.me/theorems/345e098a-91bf-4c7a-a840-c6a12961b2bb
-- title:
--   Original zero-jump Levy Gaussian centred Laplace identity at fixed time
-- statement:
--   For a genuine source spectrally negative Levy process with zero Levy jump measure, the expectation of exp(theta times its centred increment at a deterministic time) is exp(time times sigma squared theta squared over two), for nonnegative theta. This uses only the actual source process and Laplace-exponent definition, and gives a precursor to Brownian identification without adding Brownian assumptions.
-- source:
--   Original SpectrallyNegativeLevy.laplace field and laplaceExponent definition, Avram Palmowski Pistorius section 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * (Y.X t ω - (t : ℝ) * Y.c)) ∂P) =
      Real.exp ((t : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2)) := by sorry
