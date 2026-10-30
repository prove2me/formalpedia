-- Prove2me | solution 1 for finite_predicate_has_maximum__p2m_732ef142_c02d_434e_9b88_adbee85d4bda_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:43.940052+00:00
-- url     : https://prove2.me/submissions/8a59b707-9cec-4101-a5ac-11e0bb9703f4

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)