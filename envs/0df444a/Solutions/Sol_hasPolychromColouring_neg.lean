-- Prove2me | solution 1 for hasPolychromColouring_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:37:09.178925+00:00
-- url     : https://prove2.me/submissions/4cefbdf2-5947-48b5-8b31-3d173035bb54

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_IsPolychrom_neg
import Theorems.Thm_HasPolychromColouring_neg__f341ff

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
theorem _root_.solution [DecidableEq G] :
    HasPolychromColouring K (-S) ↔ HasPolychromColouring K S :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩
