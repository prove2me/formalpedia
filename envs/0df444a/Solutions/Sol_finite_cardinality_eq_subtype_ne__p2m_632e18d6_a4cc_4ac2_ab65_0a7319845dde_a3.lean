-- Prove2me | solution 1 for finite_cardinality_eq_subtype_ne__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:15:47.478982+00:00
-- url     : https://prove2.me/submissions/0c1d3940-8a3a-4e64-abf2-f460310b89a6

import Mathlib

set_option linter.style.haveILetI false

theorem solution {α : Type} [Finite α] (a : α) :
    Nat.card α = Nat.card {x : α // x ≠ a} + 1 := by
  classical
  letI := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card]
  have hcompl : Fintype.card {x : α // x ≠ a} =
      Fintype.card α - Fintype.card {x : α // x = a} := by
    exact Fintype.card_subtype_compl (p := fun x : α => x = a)
  have hone : Fintype.card {x : α // x = a} = 1 := Fintype.card_subtype_eq a
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hcompl, hone]
  omega
