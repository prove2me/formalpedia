-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_finiteLatticeCubeStep_enorm_le_of_cube_dom
-- name    : Auto.aux_CuboidNorm.finiteLatticeCubeStep_enorm_le_of_cube_dom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:02.03578+00:00
-- url     : https://prove2.me/theorems/8a7884a6-daf0-561b-b221-efb24354e9ef
-- title:
--   aux Cuboid Norm: finite Lattice Cube Step enorm le of cube dom
-- statement:
--   The aux Cuboid Norm construction uses the finite Lattice Cube Step enorm le of cube dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1799-L1820
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1799-L1820

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

theorem Auto.aux_CuboidNorm.finiteLatticeCubeStep_enorm_le_of_cube_dom {n : ℕ}
    {ε c : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n))
    (a : ZVector n → ℝ) (G : RVector n → ℝ)
    (hdom : ∀ k, k ∈ A → ∀ x, x ∈ latticeCuboid ε k →
      ‖c * a k‖ₑ ≤ ‖G x‖ₑ) :
    ∀ x, ‖finiteLatticeCubeStep ε A (fun k ↦ c * a k) x‖ₑ ≤ ‖G x‖ₑ := by sorry
