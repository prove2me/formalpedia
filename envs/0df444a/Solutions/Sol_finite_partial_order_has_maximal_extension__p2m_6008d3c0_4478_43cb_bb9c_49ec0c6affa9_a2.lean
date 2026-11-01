-- Prove2me | solution 1 for finite_partial_order_has_maximal_extension__p2m_6008d3c0_4478_43cb_bb9c_49ec0c6affa9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:15.669594+00:00
-- url     : https://prove2.me/submissions/efe84443-0fd2-4c77-8cf6-0503b9b9336c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] [PartialOrder α] (a : α) :
    ∃ b : α, a ≤ b ∧ ∀ c : α, b ≤ c → c = b := by
  classical
  let S : Set α := {b | a ≤ b}
  have hS_nonempty : S.Nonempty := ⟨a, le_rfl⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨b, hb⟩ := hS_finite.exists_maximal hS_nonempty
  refine ⟨b, hb.1, ?_⟩
  intro c hbc
  exact le_antisymm (hb.2 (show c ∈ S from le_trans hb.1 hbc) hbc) hbc