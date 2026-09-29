-- Prove2me | solution 1 for mme_finite_variance_lower_tail_gap_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:33:51.376611+00:00
-- url     : https://prove2.me/submissions/b18f23d9-c8f4-42c8-8190-f2e339c58862

import Mathlib

open BigOperators

set_option autoImplicit false

/-- A finite variance budget bounds the number of samples lying a fixed gap
below a reference value. -/
theorem solution
    {Ω : Type} [DecidableEq Ω]
    (U : Finset Ω) (f : Ω → ℝ) (μ δ V : ℝ)
    (hδ : 0 ≤ δ)
    (hvar : ∑ ω ∈ U, (f ω - μ) ^ 2 ≤ V) :
    δ ^ 2 * ((U.filter (fun ω => f ω + δ ≤ μ)).card : ℝ) ≤ V := by
  let Bad := U.filter (fun ω => f ω + δ ≤ μ)
  have hpoint : ∀ ω ∈ Bad, δ ^ 2 ≤ (f ω - μ) ^ 2 := by
    intro ω hω
    have htail := (Finset.mem_filter.mp hω).2
    nlinarith [sq_nonneg (f ω - μ + δ)]
  calc
    δ ^ 2 * (Bad.card : ℝ) = ∑ _ω ∈ Bad, δ ^ 2 := by
      simp [mul_comm]
    _ ≤ ∑ ω ∈ Bad, (f ω - μ) ^ 2 := Finset.sum_le_sum hpoint
    _ ≤ ∑ ω ∈ U, (f ω - μ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro i hiU hiBad; positivity)
    _ ≤ V := hvar
