-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_enorm_mul_le_enorm_mul_of_nonneg_le
-- name    : Auto.aux_CuboidNorm.enorm_mul_le_enorm_mul_of_nonneg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:16.561043+00:00
-- url     : https://prove2.me/theorems/9712be7a-7e15-4167-be0c-548ea371b321
-- title:
--   aux Cuboid Norm: enorm mul le enorm mul of nonneg le
-- statement:
--   A nonnegative lower coefficient can be moved through a real scalar
--   multiple inside the extended norm.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1865-L1872
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1865-L1872

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

theorem Auto.aux_CuboidNorm.enorm_mul_le_enorm_mul_of_nonneg_le {c w h : ℝ}
    (hc : 0 ≤ c) (hcw : c ≤ w) :
    ‖c * h‖ₑ ≤ ‖w * h‖ₑ := by sorry
