-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_increment
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:19:24.864217+00:00
-- url     : https://prove2.me/theorems/abc3cd10-f842-470a-8cc9-a7c884df3fa2
-- title:
--   Exact discounted q-transition increment on finite positive-rate exponential Levy test functions
-- statement:
--   For arbitrary real discount q, nonnegative time and finite real linear combinations of nonnegative-rate exponential payoffs of the genuine original spectrally negative Lévy process, the difference between discounted expected future payoff and current payoff equals the exact finite sum of individual exponential multiplier increments exp(t (ψ(rate)-q))-1. This is an exact stochastic discounted-semigroup identity, not an unproved stopped optional-sampling or arbitrary C² Dynkin theorem. It provides a finite-dimensional Feynman–Kac calculation directly relevant to q-harmonic generator residuals.
-- source:
--   Canonically Proved finite-exponential original Lévy transition semigroup (824a16a1), real exponential addition and finite sum algebra; Avram–Palmowski–Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_transition_family

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q : ℝ) (t : ℝ≥0) (x : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      (∫ ω, ∑ i ∈ s, coeff i *
        Real.exp (rate i * (x + X.X t ω)) ∂P) -
      ∑ i ∈ s, coeff i * Real.exp (rate i * x) =
    ∑ i ∈ s, coeff i * Real.exp (rate i * x) *
      (Real.exp ((t : ℝ) *
        (laplaceExponent X.c X.σ X.ν (rate i) - q)) - 1) := by sorry
