-- Prove2me | solution 1 for finite_preorder_has_maximal_element__p2m_781dd872_d82b_41cd_92b7_3c4cf55153dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:40:05.521518+00:00
-- url     : https://prove2.me/submissions/06a1196f-54f8-4fe0-9c94-c44df1f22075

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [Preorder α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a ∈ S, ∀ b, a ≤ b → b ∈ S → b ≤ a := by
  obtain ⟨a, haS, ha⟩ := (Set.toFinite S).exists_maximal hS
  refine ⟨a, haS, ?_⟩
  intro b hab hb
  exact ha hb hab