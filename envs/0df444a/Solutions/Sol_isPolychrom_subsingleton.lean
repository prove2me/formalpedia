-- Prove2me | solution 1 for isPolychrom_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:09.081096+00:00
-- url     : https://prove2.me/submissions/bcd73728-07e3-4476-867f-d3c2c33a11ce

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
theorem _root_.solution [Subsingleton K] (hS : S.Nonempty) :
    IsPolychrom S χ := by
  intro n k
  obtain ⟨i, hi⟩ := hS
  exact ⟨_, hi, Subsingleton.elim _ _⟩
