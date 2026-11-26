-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_volume_cuboid
-- name    : Auto.aux_CuboidNorm.volume_cuboid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:18.076026+00:00
-- url     : https://prove2.me/theorems/65713fb8-fd9c-5278-a6a3-56260e0eba4b
-- title:
--   aux Cuboid Norm: volume cuboid
-- statement:
--   The aux Cuboid Norm construction uses the volume cuboid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1246-L1248
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1246-L1248

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

theorem Auto.aux_CuboidNorm.volume_cuboid {n : ℕ} (l u : RVector n) :
    volume (cuboid l u) = ∏ j, ENNReal.ofReal (u j - l j) := by sorry
