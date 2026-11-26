-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_mem_latticeAxisCuboid_iff
-- name    : Auto.aux_CuboidNorm.mem_latticeAxisCuboid_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:55.457642+00:00
-- url     : https://prove2.me/theorems/231890a8-b4d3-4cef-bd76-b2daa79c682d
-- title:
--   aux Cuboid Norm: mem lattice Axis Cuboid iff
-- statement:
--   The floor description of the cuboid lift agrees with the corresponding
--   half-open translated cuboid.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1270-L1327
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1270-L1327

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

theorem Auto.aux_CuboidNorm.mem_latticeAxisCuboid_iff {n : ℕ} {ε δ : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (k : ZVector n) (y : RVector n) :
    y ∈ latticeAxisCuboid ε δ i k ↔
      (∀ j,
        if j = i then
          ε ≤ y j - (⌊y j⌋ : ℝ) ∧ y j - (⌊y j⌋ : ℝ) < ε + δ
        else
          0 ≤ y j - (⌊y j⌋ : ℝ) ∧ y j - (⌊y j⌋ : ℝ) < ε) ∧
        (fun j ↦ ⌊y j⌋) = k := by sorry
