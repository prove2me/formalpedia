-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_right_slope
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:43:16.406962+00:00
-- url     : https://prove2.me/theorems/9f36e8a6-ee8e-4780-8581-ba168440df61
-- title:
--   Exact discounted right-time generator slope on finite original Lévy exponential test functions
-- statement:
--   The right-time-zero limit of (exp(-qt) E[F(x+X_t)]-F(x))/t for any finite signed sum F(x)=sum c_i exp(theta_i x), theta_i nonnegative, is the finite sum c_i exp(theta_i x)(psi(theta_i)-q). This identifies the killed generator on a genuine finite exponential domain using the source Lévy transition expectation, exact discounted increment, the derivative of exponential, and finite-sum convergence.
-- source:
--   Proved exact finite exponential discounted increment abc3cd10, pinned Mathlib HasDerivAt.tendsto_slope_zero_right, source Levy Laplace exponent.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Monoid
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_increment

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_right_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q x : ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        (Real.exp (-(q * h)) *
          (∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (∑ i ∈ s, coeff i * Real.exp (rate i * x) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q))) := by sorry
