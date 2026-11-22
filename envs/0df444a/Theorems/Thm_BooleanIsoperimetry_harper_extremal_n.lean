-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_extremal_n
-- name    : BooleanIsoperimetry.harper_extremal_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:26.139859+00:00
-- url     : https://prove2.me/theorems/357a74df-6a2b-46e5-8149-10fcacfa9482
-- title:
--   Boolean Isoperimetry: harper extremal n
-- statement:
--   The level-`n` Harper extremal inequality, extracted from the induction
--   hypothesis `ih` (at `m = n`) and packaged for canonical cascade splits.
--
--   Given the canonical cascade split `(p, q)` of `a + b` at level `n`, its cross
--   boundary cost is no larger than that of the arbitrary split `(a, b)`.  This is
--   exactly `ih n` rewritten through `H_succ_cascade`; it is the *one-dimension-lower*
--   Macaulay/Harper extremal statement, used as a tool for the genuine
--   `n → n+1` inductive step below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L459-L466
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L459-L466

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

theorem BooleanIsoperimetry.harper_extremal_n (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by sorry
