-- Prove2me | solution 1 for isPolychrom_univ_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:13.287909+00:00
-- url     : https://prove2.me/submissions/afe64266-234e-4dd9-865f-ef42623049d3

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
theorem _root_.solution [Fintype G] :
    IsPolychrom univ (id : G → G) := by classical simp [isPolychrom_iff]
