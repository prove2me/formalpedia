-- Prove2me | solution 1 for finite_predicate_has_maximal__p2m_5e5b150a_02d6_4c7e_b48f_ee76aa630368_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:05.057691+00:00
-- url     : https://prove2.me/submissions/7c288a96-dca5-40ba-8589-2fe1b4ff1608

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α] (p : α → Prop)
    (hp : ∃ x, p x) :
    ∃ m, p m ∧ ∀ x, p x → m ≤ x → x ≤ m := by
  have hwf : WellFounded (fun a b : α => b < a) :=
    Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨m, hm, hmax⟩ := hwf.has_min {x | p x} hp
  refine ⟨m, hm, ?_⟩
  intro x hx hmx
  by_contra hxm
  exact hmax x hx (lt_of_le_of_ne hmx (Ne.symm (ne_of_not_le hxm)))