-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_split_add
-- name    : BooleanIsoperimetry.cascade_split_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:46.167853+00:00
-- url     : https://prove2.me/theorems/203570f1-ad87-4075-b646-f694f99f7734
-- title:
--   Boolean Isoperimetry: cascade split add
-- statement:
--   The two components of a cascade split add back to the split mass.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L488-L491
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L488-L491

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

theorem BooleanIsoperimetry.cascade_split_add {n k p q : ℕ} (h : CascadeSplit n k p q) : p + q = k := by sorry
