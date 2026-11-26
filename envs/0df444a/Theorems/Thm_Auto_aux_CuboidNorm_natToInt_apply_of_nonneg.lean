-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_natToInt_apply_of_nonneg
-- name    : Auto.aux_CuboidNorm.natToInt_apply_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:21.831934+00:00
-- url     : https://prove2.me/theorems/46af87c8-67a3-4ba6-a06c-382666116877
-- title:
--   aux Cuboid Norm: nat To Int apply of nonneg
-- statement:
--   The aux Cuboid Norm construction uses the nat To Int apply of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2064-L2067
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2064-L2067

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

theorem Auto.aux_CuboidNorm.natToInt_apply_of_nonneg {n : ℕ}
    (F : (Fin n → ℕ) → ℝ) (k : ZVector n) (hk : ∀ i, 0 ≤ k i) :
    aux_natToInt F k = F fun i ↦ (k i).toNat := by sorry
