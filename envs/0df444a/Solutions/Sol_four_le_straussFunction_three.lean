-- Prove2me | solution 1 for four_le_straussFunction_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:56:39.35068+00:00
-- url     : https://prove2.me/submissions/dce673c1-5a70-4467-b296-93305faa7b52

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_zero
import Theorems.Thm_lt_straussFunction_of_polychromNumber
import Theorems.Thm_straussFunction_one
import Theorems.Thm_straussFunction_two
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_mBound_ne_zero
import Theorems.Thm_mBound_one
import Theorems.Thm_mBound_pos
import Theorems.Thm_mBound_zero
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_three_eq_two
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
theorem _root_.solution : 4 ≤ straussFunction 3 := by
  suffices #({0, 1, 3} : Finset ℤ) < straussFunction 3 by grind
  apply lt_straussFunction_of_polychromNumber (by simp)
  rw [polychromNumber_three_eq_two]
  simp
