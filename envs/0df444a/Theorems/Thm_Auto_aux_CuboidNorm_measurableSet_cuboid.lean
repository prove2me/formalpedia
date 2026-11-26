-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_cuboid
-- name    : Auto.aux_CuboidNorm.measurableSet_cuboid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:17.8578+00:00
-- url     : https://prove2.me/theorems/314cd976-6594-5993-a988-2ceff3a28c77
-- title:
--   aux Cuboid Norm: measurable Set cuboid
-- statement:
--   The aux Cuboid Norm construction uses the measurable Set cuboid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1241-L1244
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1241-L1244

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

theorem Auto.aux_CuboidNorm.measurableSet_cuboid {n : ℕ} (l u : RVector n) :
    MeasurableSet (cuboid l u) := by sorry
