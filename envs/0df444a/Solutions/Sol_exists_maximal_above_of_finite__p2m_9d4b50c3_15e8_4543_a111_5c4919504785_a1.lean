-- Prove2me | solution 1 for exists_maximal_above_of_finite__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:45.811979+00:00
-- url     : https://prove2.me/submissions/c289ee7e-82d2-4fe3-a00f-54df29472609

import Mathlib

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α)
    (ha : P a) : ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c = b := by
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨b, hab, hb.1, ?_⟩
  intro c hbc hc
  exact (le_antisymm hbc (hb.2 hc hbc)).symm