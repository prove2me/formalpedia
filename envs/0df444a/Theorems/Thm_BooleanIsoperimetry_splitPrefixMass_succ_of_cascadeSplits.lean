-- Prove2me | Theorems.Thm_BooleanIsoperimetry_splitPrefixMass_succ_of_cascadeSplits
-- name    : BooleanIsoperimetry.splitPrefixMass_succ_of_cascadeSplits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:22.68237+00:00
-- url     : https://prove2.me/theorems/1415114c-2570-41cb-b3c3-b2cc139e908f
-- title:
--   Boolean Isoperimetry: split Prefix Mass succ of cascade Splits
-- statement:
--   The Boolean Isoperimetry construction uses the split Prefix Mass succ of cascade Splits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L1051-L1057
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L1051-L1057

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

theorem BooleanIsoperimetry.splitPrefixMass_succ_of_cascadeSplits
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1) (l : ℕ) :
    splitPrefixMass (n + 1) a b (l + 1)
      = splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l := by sorry
