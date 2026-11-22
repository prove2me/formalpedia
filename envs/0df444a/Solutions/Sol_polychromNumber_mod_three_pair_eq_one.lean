-- Prove2me | solution 1 for polychromNumber_mod_three_pair_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:49.264959+00:00
-- url     : https://prove2.me/submissions/35791498-7c92-4951-91f6-5d2c1089d5e3

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_one_le_polychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_le_of_forall
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ
attribute [local simp] polychromNumber_pair

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution : polychromNumber (G := ZMod 3) {0, 1} = 1 := by
  set S : Finset (ZMod 3) := {0, 1}
  refine le_antisymm ?hard ?easy
  case easy => exact one_le_polychromNumber (by simp [S])
  apply polychromNumber_le_of_forall
  decide
