-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_add_coordinate_mem_box
-- name    : Auto.aux_ErgodicBox.add_coordinate_mem_box
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:44:49.056869+00:00
-- url     : https://prove2.me/theorems/3401d888-3a11-594a-a587-f6c470ca0032
-- title:
--   aux Ergodic Box: add coordinate mem box
-- statement:
--   The aux Ergodic Box construction uses the add coordinate mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2919-L2931
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2919-L2931

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

theorem Auto.aux_ErgodicBox.add_coordinate_mem_box {n L M : ℕ} (k : Fin n → ℕ)
    (hk : k ∈ box n L) (i : Fin n) (m : ℕ) (hm : m < M) :
    k + aux_coordinate i m ∈ box n (L + M) := by sorry
