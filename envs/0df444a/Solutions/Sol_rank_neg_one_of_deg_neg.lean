-- Prove2me | solution 1 for rank_neg_one_of_deg_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:07.721265+00:00
-- url     : https://prove2.me/submissions/bb3bb670-a73e-43aa-b49d-bc4dc52eaf91

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_rank_neg_one_iff_unwinnable

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) (h_deg : deg D < 0) :
  rank G D = -1 := by
  rw [rank_neg_one_iff_unwinnable]
  intro h_win
  linarith [deg_winnable_nonneg G D h_win]
