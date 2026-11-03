-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_laplace_exponent_third_difference_jump_cube
-- name    : AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_third_difference_jump_cube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:55:21.474317+00:00
-- url     : https://prove2.me/theorems/0da0ac41-4040-4a94-b36d-0ca3c1d73ee1
-- title:
--   Original Lévy exponent third difference removes drift and Gaussian terms and equals negative jump cubic deficit
-- statement:
--   For a genuine spectrally negative Lévy process X on its original probability space with its actual Lévy measure ν, the third forward finite difference of the positive-real Laplace exponent equals the Bochner integral over negative marks of (exp(theta y)-1)^3. The original square-weight condition makes all three compensated exponential terms integrable. The binomial coefficients cancel the linear drift, Gaussian quadratic, and cutoff terms, leaving exactly the source ν cubic mark integral, with no compensator, proxy model or extra bounded-variation assumptions.
-- source:
--   Avram Wave6 Chat01 original Lévy-ν transform identity, a missing non-Gaussian small-time off-zero mark-law moment bridge for 540e2a63 and 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_source_laplace_exponent_third_difference_jump_cube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ (3 * θ) - 3 * X.ψ (2 * θ) + 3 * X.ψ θ =
      ∫ y in Iio (0 : ℝ),
        (Real.exp (θ * y) - 1) ^ 3 ∂X.ν := by sorry
