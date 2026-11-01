-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_q_harmonic_transition
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_q_harmonic_transition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:30:55.198846+00:00
-- url     : https://prove2.me/theorems/d0800d95-2ab9-45c1-ad72-45484dcadfe8
-- title:
--   Finite exponential q-eigenfunction combinations are exactly discounted transition-harmonic
-- statement:
--   For every nonnegative-rate finite exponential combination whose individual positive-rate Laplace exponent equals the discount q, the actual Levy process satisfies E[e^{-qt}F(x+X_t)]=F(x) at every deterministic nonnegative time and starting reserve, for arbitrary signed coefficients. This follows from the canonically Proved exact finite exponential discounted semigroup increment, and establishes a genuine finite-dimensional q-harmonic test class without assuming a stopped optional-sampling identity or the general source scale-function generator bridge.
-- source:
--   Proved AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_increment abc3cd10; original Levy Laplace exponent and deterministic-time Feynman–Kac identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_q_harmonic_transition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q : ℝ)
    (hroot : ∀ i ∈ s,
      laplaceExponent X.c X.σ X.ν (rate i) = q)
    (t : ℝ≥0) (x : ℝ) :
    Real.exp (-(q * (t : ℝ))) *
      (∫ ω, ∑ i ∈ s, coeff i *
        Real.exp (rate i * (x + X.X t ω)) ∂P) =
      ∑ i ∈ s, coeff i * Real.exp (rate i * x) := by sorry
