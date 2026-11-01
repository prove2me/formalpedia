-- Prove2me | solution 1 for finite_maximal_extension__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:25.566256+00:00
-- url     : https://prove2.me/submissions/807bd5b4-7eb7-4e0f-a258-8a5892b4450e

import Mathlib

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop)
    (hdown : ∀ {a b : α}, a ≤ b → P b → P a)
    (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨b, hab, hb.1, ?_⟩
  intro c hbc hc
  exact le_antisymm (hb.2 hc hbc) hbc