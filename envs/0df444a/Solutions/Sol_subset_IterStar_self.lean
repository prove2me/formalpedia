-- Prove2me | solution 1 for subset_IterStar_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:08.312735+00:00
-- url     : https://prove2.me/submissions/75c91ea8-f481-4e70-9943-06cf98fad8e7

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_epsilon_ConcatFin
import Theorems.Thm_subset_IterStar_IterFin

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution (L : Set (List A)) :
    L ⊆ L∗ := by
  have := subset_IterStar_IterFin L 1
  change IterFin L 1 ⊆ IterStar L at this
  simp [IterFin, epsilon_ConcatFin] at this
  exact this
