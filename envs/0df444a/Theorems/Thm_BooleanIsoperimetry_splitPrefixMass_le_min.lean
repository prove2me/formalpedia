-- Prove2me | Theorems.Thm_BooleanIsoperimetry_splitPrefixMass_le_min
-- name    : BooleanIsoperimetry.splitPrefixMass_le_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:17.517812+00:00
-- url     : https://prove2.me/theorems/98589743-cac8-42c0-adfd-3430b9f21ead
-- title:
--   Boolean Isoperimetry: split Prefix Mass le min
-- statement:
--   A pointwise upper bound on the prefix mass of an arbitrary split.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L973-L977
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L973-L977

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.splitPrefixMass_le_min (n a b l : ℕ) :
    splitPrefixMass n a b l ≤
      min (a + b) (binomPrefix n (l + 1) + binomPrefix n l) := by sorry
