-- Prove2me | solution 1 for finite_partial_order_exists_maximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:56:32.763874+00:00
-- url     : https://prove2.me/submissions/c8376c36-2d6c-4f51-8f27-8fab6b24e0b8

import Mathlib

theorem solution {α : Type} [Finite α] [PartialOrder α] (s : Set α) (hne : s.Nonempty) : ∃ a, a ∈ s ∧ ∀ b, b ∈ s → a ≤ b → b = a := by
  obtain ⟨a, ha⟩ := s.toFinite.exists_maximal hne
  exact ⟨a, ha.1, fun b hb hab => (ha.eq_of_le hb hab).symm⟩
