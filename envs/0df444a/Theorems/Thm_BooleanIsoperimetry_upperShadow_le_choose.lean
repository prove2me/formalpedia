-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadow_le_choose
-- name    : BooleanIsoperimetry.upperShadow_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:30.389329+00:00
-- url     : https://prove2.me/theorems/be0f5e7b-429e-4d99-9d6b-3a6be80a139a
-- title:
--   Boolean Isoperimetry: upper Shadow le choose
-- statement:
--   Kruskal–Katona/Macaulay upper bound: the upper shadow of a partial layer
--   never exceeds the full next layer.  Sorry-free monotone consequence of
--   `upperShadow_full`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L109-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L109-L113

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

theorem BooleanIsoperimetry.upperShadow_le_choose (N r t : ℕ) (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadow N r t ≤ Nat.choose N (r + 1) := by sorry
