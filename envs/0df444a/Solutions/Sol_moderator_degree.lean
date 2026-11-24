-- Prove2me | solution 1 for moderator_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:21.288017+00:00
-- url     : https://prove2.me/submissions/0a9274ef-fa84-4369-b1ac-efadc997b1d6

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} {D : CFDiv G} (h : is_moderator D) : deg D = genus G - 1 := by
  rcases h with ⟨O, hO, rfl⟩
  exact degree_ordiv O
