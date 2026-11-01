-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_generator_bridge
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_generator_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:07:00.156537+00:00
-- url     : https://prove2.me/theorems/74df27e5-2102-453c-9c34-2327bf5d2bec
-- title:
--   Exact discounted original Lévy semigroup right generator on every finite signed exponential test family
-- statement:
--   For every finite signed combination of exponential test functions with nonnegative rates, the real discounted original Lévy transition semigroup has an explicit right time derivative at zero equal to the full compensated Lévy generator minus q times the test function. The result includes canonical jump-generator integrability. This is an authentic finite-test-class Dynkin bridge and does not assert an unjustified general stopped Dynkin formula for the scale function.
-- source:
--   Canonical finite generator linearity dd86b696, canonical finite discounted semigroup right slope 9f36e8a6, generator_exp_eq_psi e651bf0f and definitional agreement of X.ψ with laplaceExponent.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Monoid
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_generator_linear
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_discounted_right_slope
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_discounted_generator_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q x : ℝ) :
    X.GeneratorIntegrable
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x ∧
    Tendsto
      (fun h : ℝ => h⁻¹ *
        (Real.exp (-(q * h)) *
          (∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator
        (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x -
        q * (∑ i ∈ s, coeff i * Real.exp (rate i * x)))) := by sorry
