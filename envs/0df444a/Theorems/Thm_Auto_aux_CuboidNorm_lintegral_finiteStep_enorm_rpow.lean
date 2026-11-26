-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteStep_enorm_rpow
-- name    : Auto.aux_CuboidNorm.lintegral_finiteStep_enorm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:45.010779+00:00
-- url     : https://prove2.me/theorems/7f7ce46c-6152-4fc0-828d-6c57ef00cac4
-- title:
--   aux Cuboid Norm: lintegral finite Step enorm rpow
-- statement:
--   The aux Cuboid Norm construction uses the lintegral finite Step enorm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1456-L1468
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1456-L1468

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
omit [DecidableEq κ]

theorem Auto.aux_CuboidNorm.lintegral_finiteStep_enorm_rpow (μ : Measure α) (A : Finset κ)
    (s : κ → Set α) (a : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (hmeas : ∀ k ∈ A, MeasurableSet (s k))
    (hdisj : ∀ ⦃k⦄, k ∈ A → ∀ ⦃l⦄, l ∈ A → k ≠ l → Disjoint (s k) (s l)) :
    (∫⁻ x, ‖finiteStep A s a x‖ₑ ^ q ∂μ) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q * μ (s k) := by sorry
