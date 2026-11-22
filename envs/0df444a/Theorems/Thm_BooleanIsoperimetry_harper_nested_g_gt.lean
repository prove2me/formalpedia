-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_nested_g_gt
-- name    : BooleanIsoperimetry.harper_nested_g_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:34.135056+00:00
-- url     : https://prove2.me/theorems/5a3456e6-ef6f-40b0-9155-7382ec802b14
-- title:
--   Boolean Isoperimetry: harper nested g gt
-- statement:
--   Clean `H (n+1)`-level form of Case II of the `n → n+1` inductive step.  Given the
--   canonical cascade split `(p, q)` of `a + b` at level `n+1`, and that the larger
--   part `a` exceeds the neighbourhood of the smaller part (`H (n+1) b < a`), the
--   split boundary sum is no larger than `H (n+1) a + a`.
--
--   This is now a short consequence of `harper_extremal_step` together with
--   `canonical_boundaryCost_eq_H_add` and the case hypotheses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1624-L1642
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1624-L1642

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

theorem BooleanIsoperimetry.harper_nested_g_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : H (n + 1) b < a)
    (_ : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by sorry
