-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_latticeAxisCuboid
-- name    : Auto.aux_CuboidNorm.measurableSet_latticeAxisCuboid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:37.54718+00:00
-- url     : https://prove2.me/theorems/2097cbe0-2558-5a0b-bf42-f7e5df05e117
-- title:
--   aux Cuboid Norm: measurable Set lattice Axis Cuboid
-- statement:
--   The aux Cuboid Norm construction uses the measurable Set lattice Axis Cuboid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1470-L1473
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1470-L1473

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

theorem Auto.aux_CuboidNorm.measurableSet_latticeAxisCuboid {n : ℕ} (ε δ : ℝ)
    (i : Fin n) (k : ZVector n) :
    MeasurableSet (latticeAxisCuboid ε δ i k) := by sorry
