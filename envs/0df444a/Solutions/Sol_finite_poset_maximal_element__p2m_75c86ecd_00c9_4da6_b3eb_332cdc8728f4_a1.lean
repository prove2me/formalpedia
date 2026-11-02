-- Prove2me | solution 1 for finite_poset_maximal_element__p2m_75c86ecd_00c9_4da6_b3eb_332cdc8728f4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:15:18.993019+00:00
-- url     : https://prove2.me/submissions/88c06f99-470d-4bb7-b392-fda833b74a7b

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ t : α, a ≤ t ∧ P t ∧ ∀ u : α, t ≤ u → P u → u = t := by
  classical
  let s : Finset α := Finset.univ.filter P
  have ha' : a ∈ s := by simp [s, ha]
  obtain ⟨t, hat, htmax⟩ := s.exists_le_maximal ha'
  refine ⟨t, hat, ?_, ?_⟩
  · have ht : t ∈ s := htmax.prop
    simpa [s] using ht
  · intro u htu hu
    have hu' : u ∈ s := by simp [s, hu]
    exact (htmax.eq_of_le hu' htu).symm