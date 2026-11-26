-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_latticeCuboid
-- name    : Auto.aux_CuboidNorm.measurableSet_latticeCuboid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:49.732935+00:00
-- url     : https://prove2.me/theorems/7e513b90-a942-409e-95a5-b03d2a4d6ad0
-- title:
--   aux Cuboid Norm: measurable Set lattice Cuboid
-- statement:
--   The aux Cuboid Norm construction uses the measurable Set lattice Cuboid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1739-L1742
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1739-L1742

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
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.measurableSet_latticeCuboid {n : ℕ} (ε : ℝ)
    (k : ZVector n) :
    MeasurableSet (latticeCuboid ε k) := by sorry
