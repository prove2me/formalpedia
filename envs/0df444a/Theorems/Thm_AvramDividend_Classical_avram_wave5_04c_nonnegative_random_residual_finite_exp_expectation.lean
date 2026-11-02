-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation
-- name    : AvramDividend.Classical.avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:33:07.867622+00:00
-- url     : https://prove2.me/theorems/78f00a57-1b6d-4a60-a593-dfce7ff697f8
-- title:
--   Bochner expectation interchange for finite exponential deficits of a nonnegative random residual
-- statement:
--   Under a probability measure, for any measurable almost surely nonnegative real random residual R, any finite set of nonnegative integer rates and arbitrary signed real coefficients, interchange the expectation and finite sum of exponential deficits. Each exponential exp(-kR) is measurable and bounded by one, hence integrable. The identity then follows from Bochner linearity and the probability normalisation of the constant one. This is an essential integrability and expectation-interchange step in the original bounded-variation Lévy C1 semigroup-generator proof.
-- source:
--   Remote compiler candidate source candidates/work_on/AvramDividend_04c_nonnegative_random_exp_deficit_integral_finset_probe.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_nonnegative_random_residual_finite_exp_expectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (R : Ω → ℝ) (hMeas : Measurable R) (hNonneg : ∀ᵐ ω ∂P, 0 ≤ R ω) (s : Finset ℕ) (coeff : ℕ → ℝ) :
    (∫ ω, ∑ k ∈ s, coeff k *
      (1 - Real.exp (-((k : ℝ) * R ω))) ∂P) =
    ∑ k ∈ s, coeff k *
      (1 - (∫ ω, Real.exp (-((k : ℝ) * R ω)) ∂P)) := by sorry
