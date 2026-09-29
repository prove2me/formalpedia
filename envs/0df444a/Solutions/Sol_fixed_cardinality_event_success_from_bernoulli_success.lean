-- Prove2me | solution 1 for fixed_cardinality_event_success_from_bernoulli_success
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:11:26.508611+00:00
-- url     : https://prove2.me/submissions/b3f9cc66-d5ea-4c0b-af39-5b249477ee9c

import Theorems.Thm_fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
import Mathlib.Tactic.Linarith

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) (epsilon : ℝ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    (∀ Omega Omega' : Finset (Fin n₁ × Fin n₂),
      Omega ⊆ Omega' → Event Omega → Event Omega') →
    bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Event ≥
      1 - epsilon →
    fixedCardinalityEventProb m Event ≥ 1 - 2 * epsilon := by
  intro hn₁ hn₂ hm hmono hbern
  have hcomparison :=
    fixed_cardinality_event_failure_le_twice_bernoulli_event_failure
      (n₁ := n₁) (n₂ := n₂) m Event hn₁ hn₂ hm hmono
  nlinarith
