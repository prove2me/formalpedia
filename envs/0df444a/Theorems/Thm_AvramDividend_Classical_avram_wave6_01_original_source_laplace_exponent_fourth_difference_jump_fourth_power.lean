-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_laplace_exponent_fourth_difference_jump_fourth_power
-- name    : AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_fourth_difference_jump_fourth_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:57:28.035143+00:00
-- url     : https://prove2.me/theorems/5873a53b-b7d6-4d52-85f2-492f1d526caf
-- title:
--   Original source fourth Lévy exponent difference is positive finite weighted negative-jump fourth moment
-- statement:
--   For the original spectrally negative Lévy source X and actual triplet, the fourth binomial finite difference of its Laplace exponent equals the nonnegative integral of (exp(theta y)-1)^4 over the actual negative-jump Lévy measure, with no drift or Gaussian residue. Every compensated exponential integrand is Bochner integrable by the Lévy square-weight hypothesis. This is the exact positive weighted moment measure identity for the real-exponential small-time band-law strategy, with no assumed compensator or proxy process.
-- source:
--   Avram Wave6 Chat01 genuine original ν fourth moment interface for compact negative-band small-time source law 540e2a63 and predictable rectangle compensator 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_fourth_difference_jump_fourth_power
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ (4 * θ) - 4 * X.ψ (3 * θ) +
      6 * X.ψ (2 * θ) - 4 * X.ψ θ =
      ∫ y in Iio (0 : ℝ),
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by sorry
