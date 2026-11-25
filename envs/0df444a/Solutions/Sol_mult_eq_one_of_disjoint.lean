-- Prove2me | solution 1 for mult_eq_one_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:55.820815+00:00
-- url     : https://prove2.me/submissions/21a8a8fd-9106-4ae5-87a1-b2c18214e2ad

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution

set_option autoImplicit true
@[expose] public section
public section
open Finset
theorem _root_.solution (k : ℕ) (A B C : Finset (Fin (3 * k)))
    (hA : A.card = k) (hB : B.card = k) (hC : C.card = k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (i : Fin (3 * k)) :
    SCCThm8.mult A B C i = 1 := by
  have hU : A ∪ B ∪ C = univ := by
    apply Finset.eq_univ_of_card
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hAC, hBC⟩),
      card_union_of_disjoint hAB, hA, hB, hC, Fintype.card_fin]
    ring
  have hi : i ∈ A ∪ B ∪ C := hU ▸ mem_univ i
  simp only [mem_union] at hi
  unfold SCCThm8.mult
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;>
    simp_all [Finset.disjoint_left]
