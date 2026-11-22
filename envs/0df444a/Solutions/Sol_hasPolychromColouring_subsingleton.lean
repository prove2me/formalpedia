-- Prove2me | solution 1 for hasPolychromColouring_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:20.440339+00:00
-- url     : https://prove2.me/submissions/764840a4-b52d-4738-a7eb-9c0988a7e1a9

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_isPolychrom_subsingleton

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
theorem _root_.solution [Nonempty K] [Subsingleton K] (hS : S.Nonempty) :
    HasPolychromColouring K S := by
  inhabit K
  exact ⟨fun _ ↦ default, isPolychrom_subsingleton hS⟩
