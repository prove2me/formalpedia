-- Prove2me | solution 1 for finite_exists_maximal__p2m_3cbfa21b_87e9_46ce_9a05_e9f44cd63dc5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:48.985992+00:00
-- url     : https://prove2.me/submissions/3ac6d153-b660-4f0b-ac79-75da2c52c0a8

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α] (S : Set α) (hne : S.Nonempty) :
    ∃ a ∈ S, ∀ b, a ≤ b → b ∈ S → b ≤ a := by
  classical
  obtain ⟨a, ha⟩ := S.toFinite.exists_maximal hne
  refine ⟨a, ha.1, ?_⟩
  intro b hab hb
  exact ha.2 hb hab