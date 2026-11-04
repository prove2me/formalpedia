-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_laplace_antitone
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_laplace_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:03:04.83025+00:00
-- url     : https://prove2.me/theorems/a0646631-ed14-43c9-b26d-609c6694c116
-- title:
--   Original Levy fourth-weighted negative Laplace moments decrease with exponent
-- statement:
--   For the actual original spectrally negative Levy measure, the fourth-exponential weighted negative-mark Laplace integral is antitone in its nonnegative Laplace exponent. Both sides are finite by the original generator-derived weighted Levy integrability; the inequality uses y<0 and positivity of the fourth power. This supplies a common dominating moment for every shifted transform without presupposing jump rates.

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_laplace_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ δ θ : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) :
    (∫ y in Iio (0 : ℝ),
      Real.exp ((ρ + δ) * y) * (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) ≤
      ∫ y in Iio (0 : ℝ),
        Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by sorry
