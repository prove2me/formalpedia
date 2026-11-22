-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice1_card_eq_cascade
-- name    : BooleanIsoperimetry.slice1_card_eq_cascade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:52.866234+00:00
-- url     : https://prove2.me/theorems/625537d6-7c3f-4103-8086-805f5d9aabff
-- title:
--   Boolean Isoperimetry: slice1 card eq cascade
-- statement:
--   The upper slice cardinality matches the cascade value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L447-L462
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L447-L462

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

theorem BooleanIsoperimetry.slice1_card_eq_cascade {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    (slice1 (simplicialInitSeg (n + 1) k)).card = cascadeSlice1Value n r t := by sorry
