-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascadeSlice1Value_le
-- name    : BooleanIsoperimetry.cascadeSlice1Value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:16.161253+00:00
-- url     : https://prove2.me/theorems/85bd4ada-1a7a-4be9-bf5d-4617669398b0
-- title:
--   Boolean Isoperimetry: cascade Slice1 Value le
-- statement:
--   The upper cascade slice value is at most `2^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L215-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L215-L220

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

theorem BooleanIsoperimetry.cascadeSlice1Value_le {n k r t : ℕ} (_ : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice1Value n r t ≤ 2 ^ n := by sorry
