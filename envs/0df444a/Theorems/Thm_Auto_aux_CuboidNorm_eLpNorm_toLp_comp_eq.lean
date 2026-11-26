-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_toLp_comp_eq
-- name    : Auto.aux_CuboidNorm.eLpNorm_toLp_comp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:39.87132+00:00
-- url     : https://prove2.me/theorems/053270d6-34fe-5653-bd92-30f9e355f2c3
-- title:
--   aux Cuboid Norm: e Lp Norm to Lp comp eq
-- statement:
--   Pulling a function back along the coordinate `WithLp` equivalence leaves
--   its `eLpNorm` unchanged, without a measurability side condition.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1674-L1684
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1674-L1684

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

theorem Auto.aux_CuboidNorm.eLpNorm_toLp_comp_eq {n : ℕ} {E : Type*}
    [TopologicalSpace E] [ENorm E] (F : ctRealVector n → E)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (fun x : RVector n ↦ F (WithLp.toLp 2 x)) p volume =
      eLpNorm F p volume := by sorry
