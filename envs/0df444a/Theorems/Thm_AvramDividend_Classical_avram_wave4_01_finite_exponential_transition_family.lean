-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_transition_family
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_transition_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:06:47.152984+00:00
-- url     : https://prove2.me/theorems/824a16a1-b664-49d1-abdf-1e52468ef786
-- title:
--   Actual Lévy transition semigroup on every finite real linear combination of positive-rate exponential test functions
-- statement:
--   For the original spectrally negative Levy process X with its exact Laplace exponent, the expectation of any finite real linear combination of exponential test payoffs equals the same finite linear combination of the corresponding exact semigroup eigenvalues, for every nonnegative time and starting reserve. Coefficients may have either sign and the rates are nonnegative, so absolute integrability follows termwise from the source Laplace axiom. This extends the Proved single-exponential identity to a finite-dimensional test class, a genuine first stage for generator-core approximation, without asserting the unresolved Ito formula for arbitrary smooth functions or the stopped Dynkin result.
-- source:
--   Avram, Palmowski and Pistorius (2007), generator and semigroup analysis in Section 5; finite linearity of the original Levy transition semigroup, using Proved levy_transition_exponential_eigenfunction ee03658e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_transition_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ)
    (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (t : ℝ≥0) (x : ℝ) :
    (∫ ω, ∑ i ∈ s, coeff i *
        Real.exp (rate i * (x + X.X t ω)) ∂P) =
      ∑ i ∈ s, coeff i *
        (Real.exp (rate i * x) *
          Real.exp ((t : ℝ) *
            laplaceExponent X.c X.σ X.ν (rate i))) := by sorry
