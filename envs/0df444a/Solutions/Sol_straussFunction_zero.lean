-- Prove2me | solution 1 for straussFunction_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:44.022509+00:00
-- url     : https://prove2.me/submissions/0e1ae446-f29e-4a34-9244-dbd796c77cbd

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
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



set_option autoImplicit true
open Finset
theorem _root_.solution : straussFunction 0 = 0 := by
  simp only [straussFunction, HasPolychromColouring, IsEmpty.exists_iff, imp_false, not_le,
    Nat.sInf_eq_zero, Set.mem_setOf_eq, not_lt_zero, forall_const, Set.eq_empty_iff_forall_notMem,
    not_forall, not_lt, false_or]
  intro n
  use Finset.Ico 0 n
  simp
