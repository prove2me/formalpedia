-- Prove2me | solution 1 for finite_cardinality_eq_subtype_ne__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:14:54.370382+00:00
-- url     : https://prove2.me/submissions/e889a7f5-1bc4-41ad-83b0-3be71312e0d8

import Mathlib

theorem solution {α : Type} [Fintype α] (a : α) :
    Nat.card α = Nat.card {x : α // x ≠ a} + 1 := by
  classical
  simp only [Nat.card_eq_fintype_card]
  have hcompl : Fintype.card {x : α // x ≠ a} =
      Fintype.card α - Fintype.card {x : α // x = a} := by
    exact Fintype.card_subtype_compl (p := fun x : α => x = a)
  have hone : Fintype.card {x : α // x = a} = 1 := Fintype.card_subtype_eq a
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hcompl, hone]
  omega
