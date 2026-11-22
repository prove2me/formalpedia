-- Prove2me | solution 1 for straussFunction_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:37.734966+00:00
-- url     : https://prove2.me/submissions/9748b14b-7bd7-4919-a085-b40e49d860ad

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_zero
import Theorems.Thm_straussFunction_le_of_forall
import Theorems.Thm_straussFunction_pos
import Theorems.Thm_hasPolychromColouring_fin_of_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_zero
import Theorems.Thm_one_le_polychromNumber
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

set_option autoImplicit true
open Finset
theorem _root_.solution : straussFunction 1 = 1 := by
  apply le_antisymm
  · apply straussFunction_le_of_forall
    intro S hS
    apply hasPolychromColouring_fin_of_le (by simp)
    apply one_le_polychromNumber
    rwa [← card_pos]
  · exact straussFunction_pos (by simp)
