-- Prove2me | solution 1 for hasPolychromColouring_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:41.095908+00:00
-- url     : https://prove2.me/submissions/c77c867f-7025-43a0-a2d9-92ea4852ca41

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_isPolychrom_univ_id

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
theorem _root_.solution [Fintype G] :
    HasPolychromColouring G (Finset.univ : Finset G) :=
  ⟨id, isPolychrom_univ_id⟩
