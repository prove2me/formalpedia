-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p
-- name    : BooleanIsoperimetry.cascade_q_le_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:52.381805+00:00
-- url     : https://prove2.me/theorems/5b568711-5e79-4df1-9490-73d9247930b5
-- title:
--   Boolean Isoperimetry: cascade q le p
-- statement:
--   In a cascade split the lower slice is at least as large as the upper slice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L494-L499
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L494-L499

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

theorem BooleanIsoperimetry.cascade_q_le_p {n k p q : ℕ} (h : CascadeSplit n k p q) : q ≤ p := by sorry
