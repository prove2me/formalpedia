-- Prove2me | solution 1 for exists_maximal_of_fintype__p2m_04119e1c_38ee_4062_845e_a21642e582fb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:19:28.394339+00:00
-- url     : https://prove2.me/submissions/aa6af3f2-26eb-4aa6-bb5f-0a89fb46c2f8

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [PartialOrder α] (S : α → Prop)
    (hS : ∃ a, S a) : ∃ a, S a ∧ ∀ b, S b → a ≤ b → b ≤ a := by
  have hfinite : ({a | S a} : Set α).Finite := Set.toFinite _
  have hnonempty : ({a | S a} : Set α).Nonempty := hS
  obtain ⟨a, ha⟩ := hfinite.exists_maximal hnonempty
  exact ⟨a, ha.1, ha.2⟩