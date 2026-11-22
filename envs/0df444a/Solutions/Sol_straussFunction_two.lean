-- Prove2me | solution 1 for straussFunction_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:55:39.572617+00:00
-- url     : https://prove2.me/submissions/058af4e9-8f10-4f8e-a513-8611356e5f77

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_zero
import Theorems.Thm_straussFunction_le_of_forall_eq
import Theorems.Thm_le_straussFunction_self
import Theorems.Thm_straussFunction_one
import Theorems.Thm_hasPolychromColouring_fin_of_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_zero
import Theorems.Thm_polychromNumber_eq_card_of_card_le_two
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] mBound_ne_zero
attribute [local simp] mBound_one
attribute [local simp] mBound_pos
attribute [local simp] mBound_zero
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


attribute [local simp] straussFunction_zero
attribute [local simp] straussFunction_one

set_option autoImplicit true
open Finset
theorem _root_.solution : straussFunction 2 = 2 := by
  apply le_antisymm
  · apply straussFunction_le_of_forall_eq
    intro S hS
    apply hasPolychromColouring_fin_of_le (by simp)
    rw [polychromNumber_eq_card_of_card_le_two hS.le, hS]
  · exact le_straussFunction_self
