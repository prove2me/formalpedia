-- Prove2me | solution 1 for finite_poset_exists_maximal_member__p2m_2e3d33d0_6b5e_40a9_a786_4b1fab836e4e_a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:09:44.823065+00:00
-- url     : https://prove2.me/submissions/92501081-783d-4258-8d0a-9cec31a91f70

import Mathlib

set_option autoImplicit false

theorem _root_.solution {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨m, hm⟩ := (Set.toFinite {x | P x}).exists_maximal ⟨a, ha⟩
  exact ⟨m, hm.1, fun b hb hmb => le_antisymm (hm.2 hb hmb) hmb⟩
