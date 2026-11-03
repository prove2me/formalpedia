-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_laplace_exponent_second_difference_levy_square
-- name    : AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_second_difference_levy_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:46:28.046186+00:00
-- url     : https://prove2.me/theorems/dfab6ecc-be1f-45de-b9a1-f1241adfd049
-- title:
--   Original Levy source exponent second difference equals Gaussian variance and positive squared-jump Laplace deficit
-- statement:
--   For the original SpectrallyNegativeLevy X with its actual triplet, the doubling finite difference of the source Laplace exponent is the exact sum sigma squared times theta squared plus the integral of the squared exponential jump deficit over the source negative Levy measure. Both individual compensated exponential integrands are integrable thanks to the actual Levy square-weight condition. This gives a positive original-source transform identity for the analytic negative-band small-time measure derivation and assumes neither a Poisson proxy nor a compensator.
-- source:
--   Avram Wave6 Chat01 missing original triplet Laplace second-difference / source Lévy measure moment identity for canonical compact-band small-time input 540e2a63 and jump compensator 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_second_difference_levy_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ (2 * θ) - 2 * X.ψ θ =
      X.σ ^ 2 * θ ^ 2 +
        ∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 2 ∂X.ν := by sorry
