-- Prove2me | solution 1 for lt_straussFunction_of_polychromNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:38.262185+00:00
-- url     : https://prove2.me/submissions/b81430c2-99f7-4110-8b76-98094770a5ae

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_zero
import Theorems.Thm_lt_straussFunction_of_not_hasPolychromColouring
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_le_polychromNumber_iff_hasPolychromColouring
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
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) {S : Finset ℤ}
    (hkS : polychromNumber S < k) :
    #S < straussFunction k := by
  apply lt_straussFunction_of_not_hasPolychromColouring hk
  rw [← le_polychromNumber_iff_hasPolychromColouring hk]
  simpa
