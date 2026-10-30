-- Prove2me | solution 1 for finite_poset_maximal_extension__p2m_bd9d7987_6824_4383_ac2f_f887fa429ccf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:40.097238+00:00
-- url     : https://prove2.me/submissions/fab6c082-c9ed-4f6b-a8bf-00e6ef72f237

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by
  obtain ⟨b, hab, hb⟩ := Finite.exists_le_maximal (p := P) ha
  refine ⟨b, hab, hb.1, ?_⟩
  intro c hbc hc
  exact le_antisymm (hb.2 hc hbc) hbc