-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_increment_lower
-- name    : BooleanIsoperimetry.H_increment_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:57.145435+00:00
-- url     : https://prove2.me/theorems/c0db5b23-f527-4249-b09c-e0ebf0d1e9a5
-- title:
--   Boolean Isoperimetry: H increment lower
-- statement:
--   The Boolean Isoperimetry construction uses the H increment lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L787-L848
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L787-L848

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

theorem BooleanIsoperimetry.H_increment_lower (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    H n p + n ≤ H n (p + 1) + p := by sorry
