-- Prove2me | solution 1 for polychromNumber_vadd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:41:27.482959+00:00
-- url     : https://prove2.me/submissions/dfe85db3-77e9-43b7-8208-75f2cb728302

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [DecidableEq G] {n : G} :
    polychromNumber (n +ᵥ S) = polychromNumber S := by simp [polychromNumber]
