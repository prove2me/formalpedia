-- Prove2me | solution 1 for mme_finite_variance_below_half_mean_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:29:54.661135+00:00
-- url     : https://prove2.me/submissions/c237b84e-fc21-479a-86a5-25534f46664b

import Mathlib

open BigOperators

set_option autoImplicit false

/-- A finite variance bound controls the number of samples at or below half
of a nonnegative mean. -/
theorem solution
    {Ω : Type} [DecidableEq Ω]
    (U : Finset Ω) (f : Ω → ℝ) (μ V : ℝ)
    (hf : ∀ ω ∈ U, 0 ≤ f ω)
    (hμ : 0 ≤ μ)
    (hvar : ∑ ω ∈ U, (f ω - μ) ^ 2 ≤ V) :
    μ ^ 2 * ((U.filter (fun ω => 2 * f ω ≤ μ)).card : ℝ) ≤ 4 * V := by
  classical
  let Bad := U.filter (fun ω => 2 * f ω ≤ μ)
  have hpoint : ∀ ω ∈ Bad, μ ^ 2 ≤ 4 * (f ω - μ) ^ 2 := by
    intro ω hω
    have hωU := (Finset.mem_filter.mp hω).1
    have hhalf := (Finset.mem_filter.mp hω).2
    have hf0 := hf ω hωU
    nlinarith [sq_nonneg (f ω - μ)]
  calc
    μ ^ 2 * (Bad.card : ℝ) = ∑ _ω ∈ Bad, μ ^ 2 := by
      simp [mul_comm]
    _ ≤ ∑ ω ∈ Bad, 4 * (f ω - μ) ^ 2 := Finset.sum_le_sum hpoint
    _ = 4 * ∑ ω ∈ Bad, (f ω - μ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 * ∑ ω ∈ U, (f ω - μ) ^ 2 := by
      gcongr
      exact Finset.filter_subset _ _
    _ ≤ 4 * V := by gcongr
