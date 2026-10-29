-- Prove2me | solution 2 for finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:16:57.868592+00:00
-- url     : https://prove2.me/submissions/009bfae6-5e97-46b2-b238-33bf4fcda4c8

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨m, -, hm⟩ := Finite.exists_le_maximal (p := P) ha
  exact ⟨m, hm.prop, fun b hb hmb => le_antisymm (hm.2 hb hmb) hmb⟩
