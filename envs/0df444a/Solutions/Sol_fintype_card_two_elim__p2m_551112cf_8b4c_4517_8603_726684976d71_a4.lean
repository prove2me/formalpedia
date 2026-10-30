-- Prove2me | solution 1 for fintype_card_two_elim__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T22:39:12.508093+00:00
-- url     : https://prove2.me/submissions/6d821eb7-70f2-4e85-858b-057dbdfe26d8

import Mathlib.Data.Fintype.Card

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α]
    (hcard : Fintype.card α = 2)
    (x y : α)
    (hxy : x ≠ y) :
    ∀ z : α, z = x ∨ z = y := by
  classical
  have hpair : ({x, y} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [Finset.card_pair hxy, hcard]
  intro z
  have hz : z ∈ ({x, y} : Finset α) := by
    rw [hpair]
    exact Finset.mem_univ z
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
