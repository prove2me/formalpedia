-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_splitPrefixMass_eq
-- name    : BooleanIsoperimetry.cascade_splitPrefixMass_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:00.596843+00:00
-- url     : https://prove2.me/theorems/0b447662-3624-4039-bac4-2eb537997bc5
-- title:
--   Boolean Isoperimetry: cascade split Prefix Mass eq
-- statement:
--   The canonical cascade split saturates the prefix-mass bound at every layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L982-L1021
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L982-L1021

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

theorem BooleanIsoperimetry.cascade_splitPrefixMass_eq {n k p q : ℕ} (h : CascadeSplit n k p q) (l : ℕ) :
    splitPrefixMass n p q l =
      min k (binomPrefix n (l + 1) + binomPrefix n l) := by sorry
