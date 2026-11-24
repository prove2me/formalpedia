-- Prove2me | solution 1 for moderator_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:19.200918+00:00
-- url     : https://prove2.me/submissions/5f1a4da7-abf2-41bb-84ae-c147b6621778

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_divisor_reverse_orientation
public import Theorems.Thm_is_acyclic_reverse_of_is_acyclic


set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (D : CFDiv G) :
  is_moderator D → is_moderator (canonical_divisor G - D) := by
  rintro ⟨O, hO, h_D⟩
  use O.reverse
  constructor
  · exact is_acyclic_reverse_of_is_acyclic G O hO
  · rw [h_D]
    rw [← divisor_reverse_orientation O]
    abel
