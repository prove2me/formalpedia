-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_finiteStep_apply_of_mem
-- name    : Auto.aux_CuboidNorm.finiteStep_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:24.569217+00:00
-- url     : https://prove2.me/theorems/bc826bbc-0df1-4841-ae74-cf65303ad334
-- title:
--   aux Cuboid Norm: finite Step apply of mem
-- statement:
--   The aux Cuboid Norm construction uses the finite Step apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1396-L1410
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1396-L1410

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

theorem Auto.aux_CuboidNorm.finiteStep_apply_of_mem (A : Finset κ) (s : κ → Set α)
    (a : κ → ℝ)
    (hdisj : ∀ ⦃k⦄, k ∈ A → ∀ ⦃l⦄, l ∈ A → k ≠ l → Disjoint (s k) (s l))
    {k : κ} (hk : k ∈ A) {x : α} (hx : x ∈ s k) :
    finiteStep A s a x = a k := by sorry
