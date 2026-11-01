-- Prove2me | solution 1 for finite_family_maximum__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:54.161223+00:00
-- url     : https://prove2.me/submissions/e40eed53-7917-48af-ac6e-67b5651941bb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (P : α → Prop) (measure : α → Nat)
    (hex : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → measure b ≤ measure a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hex with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s measure hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)