-- Prove2me | solution 1 for subset_IterStar_IterFin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:18:50.648178+00:00
-- url     : https://prove2.me/submissions/85aee7e7-499e-4e69-8529-436c9bfc73f2

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution (L : Set (List A)) (n : ℕ) :
    L ^ n ⊆ L∗ := by
  apply subset_iUnion
