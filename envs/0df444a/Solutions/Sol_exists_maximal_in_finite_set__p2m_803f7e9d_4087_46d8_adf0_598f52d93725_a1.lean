-- Prove2me | solution 1 for exists_maximal_in_finite_set__p2m_803f7e9d_4087_46d8_adf0_598f52d93725_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:12.476224+00:00
-- url     : https://prove2.me/submissions/832e61bf-6278-4c3e-9b8e-67ceefb2cc63

import Mathlib

theorem solution {α : Type} [Finite α] [Preorder α] (s : Set α) (hne : s.Nonempty) :
    ∃ a, a ∈ s ∧ ∀ b, b ∈ s → a ≤ b → b ≤ a := by
  simpa [Maximal] using s.toFinite.exists_maximal hne