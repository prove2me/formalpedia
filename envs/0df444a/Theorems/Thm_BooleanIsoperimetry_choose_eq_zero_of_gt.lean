-- Prove2me | Theorems.Thm_BooleanIsoperimetry_choose_eq_zero_of_gt
-- name    : BooleanIsoperimetry.choose_eq_zero_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:14.250531+00:00
-- url     : https://prove2.me/theorems/b862d723-6b95-4f88-a9c6-a243713d5320
-- title:
--   Boolean Isoperimetry: choose eq zero of gt
-- statement:
--   The Boolean Isoperimetry construction uses the choose eq zero of gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L122-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L122-L123

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.choose_eq_zero_of_gt {n r : ℕ} (h : n < r) : Nat.choose n r = 0 := by sorry
