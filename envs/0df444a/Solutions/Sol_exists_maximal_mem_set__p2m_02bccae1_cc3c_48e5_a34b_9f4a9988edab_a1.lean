-- Prove2me | solution 1 for exists_maximal_mem_set__p2m_02bccae1_cc3c_48e5_a34b_9f4a9988edab_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:40.875096+00:00
-- url     : https://prove2.me/submissions/982c7888-0196-4b32-b044-10222ee0f6aa

import Mathlib

theorem _root_.solution {α : Type} [Finite α] [PartialOrder α] (s : Set α) (hne : s.Nonempty) : ∃ a, a ∈ s ∧ ∀ b, a ≤ b → b ∈ s → b ≤ a := by
  obtain ⟨a, ha⟩ := s.toFinite.exists_maximal hne
  exact ⟨a, ha.1, fun b hab hb => ha.2 hb hab⟩
