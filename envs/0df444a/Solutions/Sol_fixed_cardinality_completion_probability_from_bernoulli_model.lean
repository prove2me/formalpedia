-- Prove2me | solution 1 for fixed_cardinality_completion_probability_from_bernoulli_model
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:26.814152+00:00
-- url     : https://prove2.me/submissions/1f0f9d65-333e-47a8-8ffd-f2f5b35e3fb8

import Theorems.Thm_fixed_cardinality_event_success_from_bernoulli_success
import Theorems.Thm_completion_success_event_monotone
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    (n₁ n₂ m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ) (c β : ℝ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 0 < c → 2 < β →
    bernoulliSuccessProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) M ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    successProb m M ≥
        1 - (2 * c) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hn₁ hn₂ hm _hc _hβ hbern
  have hfixed :=
    fixed_cardinality_event_success_from_bernoulli_success
      (n₁ := n₁) (n₂ := n₂) m
      (fun Omega => IsUniqueMinimizer Omega M)
      (c * Real.rpow (↑(max n₁ n₂)) (-β))
      hn₁ hn₂ hm
      (completion_success_event_monotone M)
      (by simpa [bernoulliSuccessProb] using hbern)
  unfold successProb
  simpa [fixedCardinalityEventProb, mul_assoc, mul_left_comm, mul_comm] using hfixed
