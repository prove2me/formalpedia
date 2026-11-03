-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_shifted_fourth_laplace_difference_weighted_jump_moment
-- name    : AvramDividend.Classical.avram_wave6_01_original_source_shifted_fourth_laplace_difference_weighted_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:25:29.765828+00:00
-- url     : https://prove2.me/theorems/00b5cac0-fe07-4563-bc21-b8a51eaf4d70
-- title:
--   Original source shifted fourth Laplace difference identifies every weighted Lévy exponential moment
-- statement:
--   For the same original spectrally negative Lévy process and its actual Lévy triplet, a fourth finite difference of the Laplace exponent shifted by any nonnegative base rate lambda equals the finite signed Lévy integral of exp(lambda y)(exp(theta y)-1)^4. This supplies exactly the nonnegative weighted moments needed to recover compact negative jump bands from the original small-time increment law, without assuming a jump compensator or replacing the sample space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_source_shifted_fourth_laplace_difference_weighted_jump_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    X.ψ (ρ + 4 * θ) - 4 * X.ψ (ρ + 3 * θ) +
      6 * X.ψ (ρ + 2 * θ) - 4 * X.ψ (ρ + θ) + X.ψ ρ =
      ∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by sorry
