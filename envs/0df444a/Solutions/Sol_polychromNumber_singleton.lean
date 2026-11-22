-- Prove2me | solution 1 for polychromNumber_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:42:16.429169+00:00
-- url     : https://prove2.me/submissions/3c369e6f-219d-445b-8d8b-3a3cb8ac6fe5

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_one_le_polychromNumber
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {x : G} : polychromNumber {x} = 1 :=
  (polychromNumber_le_card.trans (by simp)).antisymm (one_le_polychromNumber (by simp))
