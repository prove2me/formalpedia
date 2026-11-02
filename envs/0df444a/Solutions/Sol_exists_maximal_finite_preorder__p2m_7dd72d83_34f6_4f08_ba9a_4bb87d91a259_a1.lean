-- Prove2me | solution 1 for exists_maximal_finite_preorder__p2m_7dd72d83_34f6_4f08_ba9a_4bb87d91a259_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:13:59.286062+00:00
-- url     : https://prove2.me/submissions/d1eb54ea-c0d0-4cc2-b0d7-ba976f2331e3

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Finite α] (R : α → α → Prop) (P : α → Prop)
    (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → R a b → R b a := by
  classical
  letI : Preorder α := {
    le := R
    le_refl := hrefl
    le_trans := htrans
  }
  obtain ⟨a, ha, hmax⟩ := (Set.toFinite {a | P a}).exists_maximal ⟨hne.choose, hne.choose_spec⟩
  refine ⟨a, ha, ?_⟩
  intro b hb hab
  have hab' : a ≤ b := by
    change R a b
    exact hab
  have hba' : b ≤ a := hmax hb hab'
  change R b a
  exact hba'