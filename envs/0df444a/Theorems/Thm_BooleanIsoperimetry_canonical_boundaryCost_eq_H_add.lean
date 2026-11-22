-- Prove2me | Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
-- name    : BooleanIsoperimetry.canonical_boundaryCost_eq_H_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:05.826267+00:00
-- url     : https://prove2.me/theorems/76428a44-1537-4628-bd5b-7c7202e0e13a
-- title:
--   Boolean Isoperimetry: canonical boundary Cost eq H add
-- statement:
--   The genuine inductive content of Harper's inequality, isolated as a single
--   statement with the induction hypothesis `ih` supplied explicitly.  This is the
--   *sole remaining open step*: it is exactly the inductive step of Harper's
--   vertex-isoperimetric theorem ("the canonical cascade split minimises the cross
--   boundary expression"), which is not currently in Mathlib.
--
--   Given the canonical cascade split `(p, q)` of `a + b` (so
--   `H (n+1) (a+b) = max (H n p) q + max (H n q) p` by `H_succ_cascade`), and given
--   Harper's inequality at all strictly smaller dimensions (`ih`), the canonical
--   split has boundary value no larger than the value of any other split `(a, b)`.
--
--   It is stated non-circularly: it refers only to `H`, `CascadeSplit`, and the
--   induction hypothesis `ih`, never to `boundaryCost`, `CascadeInterleaves`,
--   `H_inequality_core`, or any later result that ultimately depends on it.
--
--   WHAT IS KNOWN (verified by computation for `n ≤ 4`):  after reducing the left
--   side to `H n p + H n q` (using `q ≤ p ≤ H n q` from the cascade), and taking
--   `a ≥ b` by symmetry, the goal splits into
--     * Case I (`a ≤ H n b`):  `H n p + H n q ≤ H n a + H n b`;
--     * Case II (`a > H n b`): `H n p + H n q ≤ H n a + a`.
--   Both are true; closing them is the missing combinatorial heart (a compression /
--   nested-cascade interleaving argument using `ih`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L364-L374
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L364-L374

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

theorem BooleanIsoperimetry.canonical_boundaryCost_eq_H_add
    {n k p q : ℕ} (hp : p ≤ 2 ^ n) (_hq : q ≤ 2 ^ n) (hq_pos : 1 ≤ q)
    (h_casc : CascadeSplit n k p q) :
    max (H n p) q + max (H n q) p = H n p + H n q := by sorry
