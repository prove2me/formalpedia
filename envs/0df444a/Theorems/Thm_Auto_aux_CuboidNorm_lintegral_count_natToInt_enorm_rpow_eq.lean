-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_lintegral_count_natToInt_enorm_rpow_eq
-- name    : Auto.aux_CuboidNorm.lintegral_count_natToInt_enorm_rpow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:59.649113+00:00
-- url     : https://prove2.me/theorems/dea6c0ed-215c-5c14-8670-14e5927e75de
-- title:
--   aux Cuboid Norm: lintegral count nat To Int enorm rpow eq
-- statement:
--   The aux Cuboid Norm construction uses the lintegral count nat To Int enorm rpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2105-L2116
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2105-L2116

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

theorem Auto.aux_CuboidNorm.lintegral_count_natToInt_enorm_rpow_eq {n : ℕ}
    (A : Finset (Fin n → ℕ)) (F : (Fin n → ℕ) → ℝ)
    (hsupport : ∀ k, k ∉ A → F k = 0) (q : ℝ) (hq : 0 < q) :
    (∫⁻ z, ‖aux_natToInt F z‖ₑ ^ q ∂Measure.count) =
      ∫⁻ k, ‖F k‖ₑ ^ q ∂Measure.count := by sorry
