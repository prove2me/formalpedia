-- Prove2me | solution 1 for finite_maximal_element__p2m_7264886b_0cfb_4b76_9d54_df3461be3785_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:27:18.31721+00:00
-- url     : https://prove2.me/submissions/93627479-e1f7-4cf4-9a6d-20e4673b9e27

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b ≤ a := by
  have hSfin : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  obtain ⟨a, ha⟩ := hSfin.exists_maximal hS
  exact ⟨a, ha.1, ha.2⟩