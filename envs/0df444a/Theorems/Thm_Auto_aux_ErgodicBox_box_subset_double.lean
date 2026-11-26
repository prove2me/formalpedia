-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_box_subset_double
-- name    : Auto.aux_ErgodicBox.box_subset_double
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:42.660477+00:00
-- url     : https://prove2.me/theorems/8794d7a2-7afa-4ebd-ab26-fcc18d8bca33
-- title:
--   aux Ergodic Box: box subset double
-- statement:
--   The aux Ergodic Box construction uses the box subset double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2439-L2444
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2439-L2444

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.box_subset_double (n M : ℕ) :
    box n M ⊆ box n (M + M) := by sorry
