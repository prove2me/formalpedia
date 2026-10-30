-- Prove2me | solution 1 for finite_exists_max_predicate__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:04.376685+00:00
-- url     : https://prove2.me/submissions/84fd493b-6a2d-4f0c-b672-98db8554c943

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Finite α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hP
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)