-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_lower_le_of_neighbor_lt
-- name    : BooleanIsoperimetry.cascade_lower_le_of_neighbor_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:13.819576+00:00
-- url     : https://prove2.me/theorems/7bc1b416-c28a-4804-a58d-b11b696d0a12
-- title:
--   Boolean Isoperimetry: cascade lower le of neighbor lt
-- statement:
--   In the GT regime of the inductive step (the larger part `a` exceeds the
--   neighbourhood `H (n+1) b` of the smaller part `b`), the canonical lower slice
--   `p` of `a + b` is at most `a`.
--
--   Proof: if `a < p` then, since `p + q = a + b`, the upper slice satisfies
--   `q < b`; but the canonical compression gives `p ≤ H (n+1) q ≤ H (n+1) b < a`,
--   contradicting `a < p`.  This is a clean structural consequence of
--   `cascade_p_le_H_q`, `H_mono`, and `cascade_split_add`; it is non-circular
--   (it does not use any later Harper result).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L554-L563
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L554-L563

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

theorem BooleanIsoperimetry.cascade_lower_le_of_neighbor_lt {n a b p q : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q) (hq_pos : 1 ≤ q)
    (hcase : H (n + 1) b < a) : p ≤ a := by sorry
