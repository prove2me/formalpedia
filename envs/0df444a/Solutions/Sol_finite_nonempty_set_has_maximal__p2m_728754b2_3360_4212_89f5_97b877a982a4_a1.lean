-- Prove2me | solution 1 for finite_nonempty_set_has_maximal__p2m_728754b2_3360_4212_89f5_97b877a982a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:55:10.957742+00:00
-- url     : https://prove2.me/submissions/c1af514f-e6c2-4919-ba30-40c8cb69a195

import Mathlib

theorem solution {α : Type} [Finite α] [PartialOrder α] (s : Set α) (hne : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by
  obtain ⟨a, ha⟩ := s.toFinite.exists_maximal hne
  exact ⟨a, ha⟩