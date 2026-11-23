-- Prove2me | solution 1 for q_reduced_eq_chips_sub_one_chip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:23.179573+00:00
-- url     : https://prove2.me/submissions/f032d5a8-1c03-4eed-ae33-f3ca78d9bf1a

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_q_reduced_eq_chips_add_q
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : q_reduced G q D) (h_q : D q = -1) :
    D = (toConfig ⟨D, h_qred.1⟩).chips - one_chip q := by
  calc
    D = (toConfig ⟨D, h_qred.1⟩).chips + D q • one_chip q :=
      q_reduced_eq_chips_add_q G q D h_qred
    _ = (toConfig ⟨D, h_qred.1⟩).chips + (-1 : ℤ) • one_chip q := by rw [h_q]
    _ = (toConfig ⟨D, h_qred.1⟩).chips - one_chip q := by
      simp only [Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]
