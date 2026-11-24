-- Prove2me | solution 1 for unwinnable_of_moderator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:28.368862+00:00
-- url     : https://prove2.me/submissions/c533c3b4-4ca0-4d2c-a6cd-b49209c9022a

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_ordiv_unwinnable


set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} {D : CFDiv G} (h : is_moderator D) : ¬ winnable G D := by
  rcases h with ⟨O, hO, rfl⟩
  exact ordiv_unwinnable G O hO
