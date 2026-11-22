-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CascadeInterleaves_lower_succ
-- name    : BooleanIsoperimetry.CascadeInterleaves.lower_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:25.269677+00:00
-- url     : https://prove2.me/theorems/651798a5-3138-44ff-918a-83cab93ef11d
-- title:
--   Cascade Interleaves: lower succ
-- statement:
--   The Cascade Interleaves construction uses the lower succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L1059-L1070
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L1059-L1070

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

theorem BooleanIsoperimetry.CascadeInterleaves.lower_succ
    {n a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (h_inter : CascadeInterleaves (n + 1) p q a b)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1) :
    ∀ l, splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l := by sorry
