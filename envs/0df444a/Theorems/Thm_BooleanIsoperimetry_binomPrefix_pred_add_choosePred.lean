-- Prove2me | Theorems.Thm_BooleanIsoperimetry_binomPrefix_pred_add_choosePred
-- name    : BooleanIsoperimetry.binomPrefix_pred_add_choosePred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:10.688362+00:00
-- url     : https://prove2.me/theorems/42181c92-8b79-4c1f-a26b-20c71ff8042d
-- title:
--   Boolean Isoperimetry: binom Prefix pred add choose Pred
-- statement:
--   `binomPrefix n (r-1) + choosePred n r = binomPrefix n r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L161-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L161-L167

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

theorem BooleanIsoperimetry.binomPrefix_pred_add_choosePred (n r : ℕ) :
    binomPrefix n (r - 1) + choosePred n r = binomPrefix n r := by sorry
