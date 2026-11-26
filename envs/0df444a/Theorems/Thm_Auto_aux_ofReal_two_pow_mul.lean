-- Prove2me | Theorems.Thm_Auto_aux_ofReal_two_pow_mul
-- name    : Auto.aux_ofReal_two_pow_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:45:09.837388+00:00
-- url     : https://prove2.me/theorems/0242c9e5-3675-528b-b6fe-1531f624423e
-- title:
--   Auto: aux of Real two pow mul
-- statement:
--   The Auto construction uses the aux of Real two pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L3055-L3060
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L3055-L3060

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

theorem Auto.aux_ofReal_two_pow_mul (n : ℕ) (C : ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ n * C) =
      ((2 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal C := by sorry
