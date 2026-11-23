-- Prove2me | solution 1 for maximal_unwinnable_preserved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:42.599924+00:00
-- url     : https://prove2.me/submissions/264b43f0-827d-43d1-ba32-48e515fdddf1

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_winnable_equiv_winnable
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D1 D2 : CFDiv G) :
  maximal_unwinnable G D1 → linear_equiv G D1 D2 → maximal_unwinnable G D2 := by
  rintro ⟨h_unwin_D1, h_winnable_add⟩ h_lequiv
  refine ⟨?_, ?_⟩
  · intro h_win_D2
    exact h_unwin_D1 <| winnable_equiv_winnable G D2 D1 h_win_D2 h_lequiv.symm
  · intro v
    exact winnable_equiv_winnable G (D1 + one_chip v) (D2 + one_chip v) (h_winnable_add v) <| by
      unfold linear_equiv at *
      simpa only [add_sub_add_right_eq_sub] using h_lequiv
