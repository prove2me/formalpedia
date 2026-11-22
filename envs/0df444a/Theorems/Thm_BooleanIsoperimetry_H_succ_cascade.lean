-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
-- name    : BooleanIsoperimetry.H_succ_cascade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:45.491561+00:00
-- url     : https://prove2.me/theorems/3a0f7e71-2142-4007-ae13-d20b3f7b2b19
-- title:
--   Boolean Isoperimetry: H succ cascade
-- statement:
--   Recursion for `H` in terms of the canonical cascade split.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L653-L656
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L653-L656

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

theorem BooleanIsoperimetry.H_succ_cascade {n k p q : ℕ} (h : CascadeSplit n k p q) :
    H (n + 1) k = max (H n p) q + max (H n q) p := by sorry
