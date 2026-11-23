-- Prove2me | solution 1 for winnable_equiv_winnable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:17.04579+00:00
-- url     : https://prove2.me/submissions/5beb0088-9c75-401b-b76f-d7e877d2d2ac

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D1 D2 : CFDiv G) :
  winnable G D1 → linear_equiv G D1 D2 → winnable G D2 := by
  rintro ⟨D1', h_D1'_eff, h_lequiv1⟩ h_lequiv
  exact ⟨D1', h_D1'_eff, h_lequiv.symm.trans h_lequiv1⟩
