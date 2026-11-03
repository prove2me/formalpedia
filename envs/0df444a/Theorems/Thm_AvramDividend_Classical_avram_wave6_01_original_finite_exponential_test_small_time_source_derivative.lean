-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_finite_exponential_test_small_time_source_derivative
-- name    : AvramDividend.Classical.avram_wave6_01_original_finite_exponential_test_small_time_source_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:28:43.309775+00:00
-- url     : https://prove2.me/theorems/aa02aa06-7300-4d87-8808-173aebf0c9df
-- title:
--   Small-time first derivative of original Levy finite exponential test expectations
-- statement:
--   For the unchanged source SpectrallyNegativeLevy X on Ω/P/𝓕, the right-time difference quotient at zero of the expected finite real linear combination Σ_i coeff_i exp(rate_i X_t) converges to Σ_i coeff_i ψ(rate_i), where ψ is the triplet-defined Laplace exponent. All rates are nonnegative and the expectation is the original integral over P. The exact Laplace semigroup is previously Proved; this theorem establishes its genuine source-time derivative with the positive-real-to-NNReal clock boundary handled explicitly. It is a required analytic core for proving the small-time ν-band law through exponential-polynomial tests, and assumes no jump compensator.
-- source:
--   Avram Wave6 Chat01. Non-circular analytic source-law bridge from the true original finite-exponential transition formula 824a16a1 to infinitesimal Lévy triplet exponent; needed for original compact negative band small-time target 540e2a63 and ultimately intrinsic compensator 393b03a8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_transition_family

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_finite_exponential_test_small_time_source_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (coeff rate : ι → ℝ)
    (hrate : ∀ i ∈ I, 0 ≤ rate i) :
    Tendsto
      (fun h : ℝ =>
        ((∫ ω, ∑ i ∈ I, coeff i *
          Real.exp (rate i * X.X (Real.toNNReal h) ω) ∂P) -
          ∑ i ∈ I, coeff i) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ i ∈ I, coeff i *
        laplaceExponent X.c X.σ X.ν (rate i))) := by sorry
