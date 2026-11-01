-- Prove2me | solution 1 for finite_partialOrder_has_maximal_for_predicate__p2m_a870ea81_7152_406d_9ca9_18eedb61291e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:01.143135+00:00
-- url     : https://prove2.me/submissions/2a2c5c88-5788-457a-9f6e-ebce79c35b8d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) [DecidablePred P] (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  obtain ⟨a, ha⟩ := s.exists_maximal hs
  rw [maximal_iff] at ha
  refine ⟨a, ?_, ?_⟩
  · simpa [s, Finset.mem_filter] using ha.1
  · intro b hb hab
    have hb' : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    exact (ha.2 hb' hab).symm