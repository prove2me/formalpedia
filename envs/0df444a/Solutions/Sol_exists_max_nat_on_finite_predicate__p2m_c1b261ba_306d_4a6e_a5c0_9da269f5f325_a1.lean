-- Prove2me | solution 1 for exists_max_nat_on_finite_predicate__p2m_c1b261ba_306d_4a6e_a5c0_9da269f5f325_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:06.168972+00:00
-- url     : https://prove2.me/submissions/4d6b5bc0-940e-4f5b-b982-2641c2c78ed2

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (P : α → Prop) (hP : ∃ a, P a) (f : α → Nat) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)