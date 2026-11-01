-- Prove2me | solution 1 for exists_maximal_element_of_finite_set__p2m_5ad4dfa2_7b03_4649_bf47_2550ad7ee6b8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:54.3162+00:00
-- url     : https://prove2.me/submissions/8200b45b-695b-4ab3-bf85-3f97fdb4dacc

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [Preorder α]
    (S : Set α) (hS : S.Finite) (hSne : S.Nonempty) :
    ∃ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a := by
  obtain ⟨a, ha⟩ := hS.exists_maximal hSne
  exact ⟨a, ha.1, fun b hb hab => ha.2 hb hab⟩