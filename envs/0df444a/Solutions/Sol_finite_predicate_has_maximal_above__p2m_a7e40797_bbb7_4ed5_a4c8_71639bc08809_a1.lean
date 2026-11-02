-- Prove2me | solution 1 for finite_predicate_has_maximal_above__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:40.392202+00:00
-- url     : https://prove2.me/submissions/d677c331-2caa-487e-aa85-2efe1899f8a3

import Mathlib

theorem solution
    {α : Type} [Preorder α] [Finite α]
    (S : α → Prop) (x : α) (hx : S x) :
    ∃ y, S y ∧ x ≤ y ∧ ∀ z, S z → y ≤ z → z ≤ y := by
  classical
  obtain ⟨y, hxy, hy⟩ := Finite.exists_le_maximal (p := S) hx
  exact ⟨y, hy.1, hxy, fun z hz hyz => hy.2 hz hyz⟩