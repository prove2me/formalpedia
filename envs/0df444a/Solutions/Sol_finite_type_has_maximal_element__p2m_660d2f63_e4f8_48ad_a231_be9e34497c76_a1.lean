-- Prove2me | solution 1 for finite_type_has_maximal_element__p2m_660d2f63_e4f8_48ad_a231_be9e34497c76_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:30:49.215167+00:00
-- url     : https://prove2.me/submissions/2101ee06-e636-4bc5-985a-768ef0fe9837

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b ≤ a := by
  classical
  have hfin : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  obtain ⟨a, ha⟩ := hfin.exists_maximal hS
  refine ⟨a, ha.1, ?_⟩
  intro b hb hab
  exact ha.2 hb hab