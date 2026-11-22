-- Prove2me | solution 1 for straussFunction_le_of_forall_three_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:56:39.836713+00:00
-- url     : https://prove2.me/submissions/49f7332a-11fa-4491-8727-818699607d8c

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_zero
import Theorems.Thm_straussFunction_le_of_forall
import Theorems.Thm_straussFunction_one
import Theorems.Thm_straussFunction_two
import Theorems.Thm_exists_colouring_of_sq_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_zero
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
attribute [local simp] straussFunction_two

set_option autoImplicit true
open Finset
theorem _root_.solution {k : ℕ} :
    straussFunction k ≤ 3 * k ^ 2 := by
-- ANCHOR_END: straussFunction_le_of_forall_three_mul_sq
  obtain rfl | hk := eq_or_ne k 0
  · simp
  apply straussFunction_le_of_forall
  intro S hS
  exact exists_colouring_of_sq_le hk (S := S) hS
