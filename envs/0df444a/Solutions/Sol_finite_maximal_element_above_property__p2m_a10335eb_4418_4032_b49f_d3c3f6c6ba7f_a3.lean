-- Prove2me | solution 1 for finite_maximal_element_above_property__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:22.183197+00:00
-- url     : https://prove2.me/submissions/e524fc65-a9e4-416d-ba03-24e27b50d633

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (Q : α → Prop) (a : α) (ha : Q a) :
    ∃ b : α, a ≤ b ∧ Q b ∧ ∀ c : α, b ≤ c → Q c → c = b := by
  classical
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := Q) ha
  refine ⟨b, hab, hb.1, ?_⟩
  intro c hbc hc
  exact le_antisymm (hb.2 hc hbc) hbc