-- Prove2me | solution 1 for rank_neg_one_of_not_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:56.33659+00:00
-- url     : https://prove2.me/submissions/c72aa79f-92fb-41ee-9d37-9dd884c0a42e

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_rank_geq_neg_one

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G)
  (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by
  have := rank_geq_neg_one G D
  omega
