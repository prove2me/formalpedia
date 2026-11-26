-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_natToInt_support_map
-- name    : Auto.aux_CuboidNorm.natToInt_support_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:23.451794+00:00
-- url     : https://prove2.me/theorems/1598eb18-fa83-442a-917f-fbc4ba98650f
-- title:
--   aux Cuboid Norm: nat To Int support map
-- statement:
--   The aux Cuboid Norm construction uses the nat To Int support map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2088-L2103
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2088-L2103

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

theorem Auto.aux_CuboidNorm.natToInt_support_map {n : ℕ} (A : Finset (Fin n → ℕ))
    (F : (Fin n → ℕ) → ℝ) (hsupport : ∀ k, k ∉ A → F k = 0) :
    ∀ z, z ∉ A.map natToIntEmbedding → aux_natToInt F z = 0 := by sorry
