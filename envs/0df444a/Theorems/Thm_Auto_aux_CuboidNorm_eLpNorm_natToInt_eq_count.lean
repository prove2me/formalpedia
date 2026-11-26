-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_natToInt_eq_count
-- name    : Auto.aux_CuboidNorm.eLpNorm_natToInt_eq_count
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:43:07.023128+00:00
-- url     : https://prove2.me/theorems/3cda32e5-b24b-4f44-957c-9b3e0fb3ce4f
-- title:
--   aux Cuboid Norm: e Lp Norm nat To Int eq count
-- statement:
--   The aux Cuboid Norm construction uses the e Lp Norm nat To Int eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2118-L2126
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2118-L2126

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

theorem Auto.aux_CuboidNorm.eLpNorm_natToInt_eq_count {n : ℕ}
    (A : Finset (Fin n → ℕ)) (F : (Fin n → ℕ) → ℝ)
    (hsupport : ∀ k, k ∉ A → F k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_natToInt F) p Measure.count = eLpNorm F p Measure.count := by sorry
