-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_cuboidEmbed_eq_finiteLatticeStep_apply
-- name    : Auto.aux_CuboidNorm.cuboidEmbed_eq_finiteLatticeStep_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:59.538597+00:00
-- url     : https://prove2.me/theorems/cef95be3-3ebf-41f6-9f2b-79537ce22915
-- title:
--   aux Cuboid Norm: cuboid Embed eq finite Lattice Step apply
-- statement:
--   A finite-support floor cuboid lift is a finite sum of disjoint
--   half-open cuboid steps.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1483-L1519
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1483-L1519

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

theorem Auto.aux_CuboidNorm.cuboidEmbed_eq_finiteLatticeStep_apply {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (y : RVector n) :
    aux_cuboidEmbed ε δ i a y = finiteLatticeStep ε δ i A a y := by sorry
