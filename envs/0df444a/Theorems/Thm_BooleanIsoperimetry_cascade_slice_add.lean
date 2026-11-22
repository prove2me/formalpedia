-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_slice_add
-- name    : BooleanIsoperimetry.cascade_slice_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:09.796549+00:00
-- url     : https://prove2.me/theorems/ec371421-6a0f-4a71-abf1-2b34daa7a6ce
-- title:
--   Boolean Isoperimetry: cascade slice add
-- statement:
--   The two cascade slice values sum to `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L197-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L197-L202

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

theorem BooleanIsoperimetry.cascade_slice_add {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice0Value n r t + cascadeSlice1Value n r t = k := by sorry
