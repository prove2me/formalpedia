-- Prove2me | solution 1 for finite_partial_order_has_maximal_element__p2m_cebdf6a5_ed21_4e3f_9527_133aad01d215_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:01:02.448619+00:00
-- url     : https://prove2.me/submissions/c8474453-a294-406a-a12e-001f02215e3b

import Mathlib

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by
  classical
  let s : Set α := {a | P a}
  have hs : s.Nonempty := by
    rcases hP with ⟨a, ha⟩
    exact ⟨a, ha⟩
  have hfin : s.Finite := Set.finite_univ.subset (by
    intro a ha
    exact Set.mem_univ a)
  obtain ⟨a, ha⟩ := hfin.exists_maximal hs
  exact ⟨a, ha.1, fun b hb hab => ha.2 hb hab⟩