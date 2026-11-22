-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_extremal_step_nested_q_zero
-- name    : BooleanIsoperimetry.harper_extremal_step_nested_q_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:49.315305+00:00
-- url     : https://prove2.me/theorems/5d9ca2fa-c3f4-46d0-b0c0-a9badd7ba0ea
-- title:
--   Boolean Isoperimetry: harper extremal step nested q zero
-- statement:
--   The degenerate top-level branch of the nested extremal step.  When the canonical
--   upper slice `q` is empty, the statement reduces to the already-proved
--   `harper_bc_min_q_zero` in dimension `n + 1` (with a symmetric `a,b` branch).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L481-L515
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L481-L515

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

theorem BooleanIsoperimetry.harper_extremal_step_nested_q_zero (n : ℕ)
    (_ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_zero : q = 0)
    (_hp0 : p0 ≤ 2 ^ n) (_hp1 : p1 ≤ 2 ^ n)
    (_hq0 : q0 ≤ 2 ^ n) (_hq1 : q1 ≤ 2 ^ n)
    (_ha0 : a0 ≤ 2 ^ n) (_ha1 : a1 ≤ 2 ^ n)
    (_hb0 : b0 ≤ 2 ^ n) (_hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (max (H n p0) p1 + max (H n p1) p0) q +
    max (max (H n q0) q1 + max (H n q1) q0) p ≤
    max (max (H n a0) a1 + max (H n a1) a0) b +
    max (max (H n b0) b1 + max (H n b1) b0) a := by sorry
