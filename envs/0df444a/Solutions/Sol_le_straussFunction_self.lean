-- Prove2me | solution 1 for le_straussFunction_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:54:39.800065+00:00
-- url     : https://prove2.me/submissions/93f00b9e-8bfb-4108-b6df-45a957bc2198

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_zero
import Theorems.Thm_lt_straussFunction_of_polychromNumber
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

set_option autoImplicit true
open Finset
theorem _root_.solution {k : ℕ} :
    k ≤ straussFunction k := by
-- ANCHOR_END: le_straussFunction_self
  obtain rfl | hk := eq_or_ne k 0
  · simp
  let S : Finset ℤ := Finset.Ico (0 : ℤ) (k - 1)
  have : #S = k - 1 := by simp [S]
  have : polychromNumber S < k := by grind [polychromNumber_le_card]
  have := lt_straussFunction_of_polychromNumber hk this
  grind
