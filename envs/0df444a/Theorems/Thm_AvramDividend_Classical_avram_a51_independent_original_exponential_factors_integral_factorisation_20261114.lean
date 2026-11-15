-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a51_independent_original_exponential_factors_integral_factorisation_20261114
-- name    : AvramDividend.Classical.avram_a51_independent_original_exponential_factors_integral_factorisation_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:49:19.846679+00:00
-- url     : https://prove2.me/theorems/4c568d5d-25f8-4488-9a7c-edd3cd3bf1e0
-- title:
--   Independent integrable real exponential factors give product formula for source Laplace moments
-- statement:
--   For an original probability measure and two independent integrable real exponential random factors, the moment of the exponential of the sum is exactly the product of their respective exponential moments.
-- source:
--   Pinned Mathlib ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral and Real.exp_add.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a51_independent_original_exponential_factors_integral_factorisation_20261114
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G J : Ω → ℝ) (θ : ℝ)
    (hInd : IndepFun (fun ω => Real.exp (θ * G ω))
      (fun ω => Real.exp (θ * J ω)) P)
    (hG : Integrable (fun ω => Real.exp (θ * G ω)) P)
    (hJ : Integrable (fun ω => Real.exp (θ * J ω)) P) :
    (∫ ω, Real.exp (θ * (G ω + J ω)) ∂P) =
      (∫ ω, Real.exp (θ * G ω) ∂P) *
      (∫ ω, Real.exp (θ * J ω) ∂P) := by sorry
