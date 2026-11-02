-- Prove2me | solution 1 for finite_maximal_by_nat_measure__p2m_6d710174_22d6_4830_a446_d998b14d2565_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:53:40.106649+00:00
-- url     : https://prove2.me/submissions/ef548a81-8b8c-4916-b9c8-01113bfc53fb

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] (P : α → Prop) (R : α → α → Prop) (measure : α → Nat)
    (hP : ∃ a, P a)
    (hstrict : ∀ a b, P a → P b → R a b → a ≠ b → measure a < measure b) :
    ∃ a, P a ∧ ∀ b, P b → R a b → a = b := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s measure hs
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb hR
  by_contra hne
  have hbmem : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩
  have hle : measure b ≤ measure a := hmax b hbmem
  exact (not_lt_of_ge hle) (hstrict a b (Finset.mem_filter.mp ha).2 hb hR hne)