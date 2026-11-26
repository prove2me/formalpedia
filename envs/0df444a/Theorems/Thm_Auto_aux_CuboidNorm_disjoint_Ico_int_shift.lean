-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_disjoint_Ico_int_shift
-- name    : Auto.aux_CuboidNorm.disjoint_Ico_int_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:34.338082+00:00
-- url     : https://prove2.me/theorems/40f55bbf-0fc0-4980-a7a4-219b80f1d1ca
-- title:
--   aux Cuboid Norm: disjoint Ico int shift
-- statement:
--   The aux Cuboid Norm construction uses the disjoint Ico int shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1339-L1353
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1339-L1353

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
open Auto.aux_CuboidNorm

theorem Auto.aux_CuboidNorm.disjoint_Ico_int_shift {c w : ℝ} (hw : w ≤ 1)
    {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (Ico ((k : ℝ) + c) ((k : ℝ) + c + w))
      (Ico ((l : ℝ) + c) ((l : ℝ) + c + w)) := by sorry
