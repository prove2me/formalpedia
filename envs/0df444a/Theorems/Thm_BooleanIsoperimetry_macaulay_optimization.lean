-- Prove2me | Theorems.Thm_BooleanIsoperimetry_macaulay_optimization
-- name    : BooleanIsoperimetry.macaulay_optimization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:55.420809+00:00
-- url     : https://prove2.me/theorems/e0506677-d320-4690-9fcd-236592d60a59
-- title:
--   Boolean Isoperimetry: macaulay optimization
-- statement:
--   The core Kruskal-Katona / Macaulay optimization inequality for the cascade split.
--   For any canonical split `(p, q)` of `a + b`, the cross-sum of their boundary sizes
--   is bounded by the sum of boundary bounds for the original sizes `a` and `b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2094-L2098
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L2094-L2098

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.macaulay_optimization {n a b p q : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (h_casc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by sorry
