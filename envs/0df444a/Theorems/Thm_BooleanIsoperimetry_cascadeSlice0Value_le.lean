-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascadeSlice0Value_le
-- name    : BooleanIsoperimetry.cascadeSlice0Value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:44.275851+00:00
-- url     : https://prove2.me/theorems/428d8de0-0e41-49ac-8498-88a4038dcbea
-- title:
--   Boolean Isoperimetry: cascade Slice0 Value le
-- statement:
--   The lower cascade slice value is at most `2^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L205-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L205-L212

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

theorem BooleanIsoperimetry.cascadeSlice0Value_le {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice0Value n r t ≤ 2 ^ n := by sorry
