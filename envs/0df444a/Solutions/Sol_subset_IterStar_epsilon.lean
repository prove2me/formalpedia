-- Prove2me | solution 1 for subset_IterStar_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:05.979518+00:00
-- url     : https://prove2.me/submissions/f84ce1ba-29e8-4918-af5a-9f59f725b799

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_subset_IterStar_IterFin

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution (L : Set (List A)) :
    {[]} ⊆ L∗ := by
  exact subset_IterStar_IterFin L 0
