-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteLatticeStep_enorm_rpow
-- name    : Auto.aux_CuboidNorm.lintegral_finiteLatticeStep_enorm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:56.582062+00:00
-- url     : https://prove2.me/theorems/49d69435-b94d-5ea0-be23-820e71ad80bb
-- title:
--   aux Cuboid Norm: lintegral finite Lattice Step enorm rpow
-- statement:
--   The aux Cuboid Norm construction uses the lintegral finite Lattice Step enorm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1521-L1531
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1521-L1531

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

theorem Auto.aux_CuboidNorm.lintegral_finiteLatticeStep_enorm_rpow {n : ℕ}
    {ε δ : ℝ} (hε : ε ≤ 1) (hδ : δ ≤ 1) (i : Fin n)
    (A : Finset (ZVector n)) (a : ZVector n → ℝ) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖finiteLatticeStep ε δ i A a x‖ₑ ^ q ∂volume) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q * volume (latticeAxisCuboid ε δ i k) := by sorry
