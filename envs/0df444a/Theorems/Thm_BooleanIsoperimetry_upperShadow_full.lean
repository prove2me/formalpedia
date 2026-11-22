-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadow_full
-- name    : BooleanIsoperimetry.upperShadow_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:52.39584+00:00
-- url     : https://prove2.me/theorems/f4749893-e926-427a-9c96-d8879e842993
-- title:
--   Boolean Isoperimetry: upper Shadow full
-- statement:
--   A complete layer has upper shadow equal to the full next layer
--   `Nat.choose N (r+1)`: the upper shadow of all of layer `r` is all of layer
--   `r+1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L98-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L98-L104

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.upperShadow_full (N r : ℕ) (hr : 1 ≤ r) :
    upperShadow N r (Nat.choose N r) = Nat.choose N (r + 1) := by sorry
