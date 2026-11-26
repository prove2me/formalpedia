-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_enorm_rpow_eq_finset
-- name    : Auto.aux_CuboidNorm.lintegral_count_enorm_rpow_eq_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:17.236807+00:00
-- url     : https://prove2.me/theorems/e6180c5e-cdc8-5e95-aea3-a3c2037c662d
-- title:
--   aux Cuboid Norm: lintegral count enorm rpow eq finset
-- statement:
--   The aux Cuboid Norm construction uses the lintegral count enorm rpow eq finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1569-L1578
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1569-L1578

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

theorem Auto.aux_CuboidNorm.lintegral_count_enorm_rpow_eq_finset {κ : Type*}
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (A : Finset κ) (a : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (hsupport : ∀ k, k ∉ A → a k = 0) :
    (∫⁻ k, ‖a k‖ₑ ^ q ∂Measure.count) = ∑ k ∈ A, ‖a k‖ₑ ^ q := by sorry
