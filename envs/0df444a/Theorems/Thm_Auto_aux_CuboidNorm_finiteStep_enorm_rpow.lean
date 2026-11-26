-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_enorm_rpow
-- name    : Auto.aux_CuboidNorm.finiteStep_enorm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:02.958842+00:00
-- url     : https://prove2.me/theorems/f3663f4a-9854-4e02-9187-157ac16c9db8
-- title:
--   aux Cuboid Norm: finite Step enorm rpow
-- statement:
--   The aux Cuboid Norm construction uses the finite Step enorm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1423-L1453
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1423-L1453

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
omit [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.finiteStep_enorm_rpow (A : Finset κ) (s : κ → Set α)
    (a : κ → ℝ) (q : ℝ) (hq : 0 < q)
    (hdisj : ∀ ⦃k⦄, k ∈ A → ∀ ⦃l⦄, l ∈ A → k ≠ l → Disjoint (s k) (s l))
    (x : α) :
    ‖finiteStep A s a x‖ₑ ^ q =
      ∑ k ∈ A, (s k).indicator (fun _ ↦ ‖a k‖ₑ ^ q) x := by sorry
