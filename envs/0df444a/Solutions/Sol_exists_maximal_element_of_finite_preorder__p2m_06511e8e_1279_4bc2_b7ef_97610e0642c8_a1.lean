-- Prove2me | solution 1 for exists_maximal_element_of_finite_preorder__p2m_06511e8e_1279_4bc2_b7ef_97610e0642c8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:38:24.94128+00:00
-- url     : https://prove2.me/submissions/e1739339-49bb-4e00-b452-f0e0b7a14649

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α]
    (P : α → Prop) (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → r a b → r b a := by
  classical
  letI : LE α := ⟨r⟩
  letI : IsTrans α (· ≤ ·) := ⟨htrans⟩
  let s : Finset α := Finset.univ.filter P
  obtain ⟨a, ha⟩ := hP
  have haS : a ∈ s := by
    simp [s, ha]
  obtain ⟨a, haS, hmax⟩ := s.exists_maximal ⟨a, haS⟩
  refine ⟨a, (Finset.mem_filter.mp haS).2, ?_⟩
  intro b hb hr
  exact hmax (by simp [s, hb]) hr