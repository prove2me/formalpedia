-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_gt_split_between
-- name    : BooleanIsoperimetry.harper_gt_split_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:55.849728+00:00
-- url     : https://prove2.me/theorems/a7282a04-fb3f-4824-bb21-442a684e8208
-- title:
--   Boolean Isoperimetry: harper gt split between
-- statement:
--   Structural "central compression" invariant of the GT regime of the positive
--   Macaulay step.  When the larger part `a` already dominates the neighbourhood of
--   the smaller part (`H (n+1) b < a`), the canonical cascade split `(p, q)` of
--   `a + b` is sandwiched between the two parts: `b ≤ q ≤ p ≤ a`.
--
--   This records that, in the slack regime, passing to the canonical split moves
--   mass strictly inward (from the `a`-side toward the `b`-side) without crossing
--   either endpoint.  It depends only on the level-`n+1` cascade structure
--   (`harper_case_gt_a_ge_p`, `cascade_q_le_p`, `cascade_split_add`) and the case
--   hypothesis, so it is non-circular and reusable in any GT-regime argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L832-L839
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L832-L839

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

theorem BooleanIsoperimetry.harper_gt_split_between (n : ℕ) {a b p q : ℕ}
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    b ≤ q ∧ q ≤ p ∧ p ≤ a := by sorry
