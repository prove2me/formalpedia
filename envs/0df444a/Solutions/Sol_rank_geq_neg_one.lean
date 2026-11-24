-- Prove2me | solution 1 for rank_geq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:17.937128+00:00
-- url     : https://prove2.me/submissions/659aac97-b690-4cff-ad51-795d618b05c4

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_rank_geq_iff

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) : rank G D ≥ -1 :=
  (rank_geq_iff G D (-1)).mp (rank_geq_neg G D (-1) (by norm_num))
