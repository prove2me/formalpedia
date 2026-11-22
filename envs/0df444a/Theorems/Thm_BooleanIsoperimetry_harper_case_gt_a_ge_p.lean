-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_case_gt_a_ge_p
-- name    : BooleanIsoperimetry.harper_case_gt_a_ge_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:16.154308+00:00
-- url     : https://prove2.me/theorems/48bb2556-528d-4ccb-99d0-1cf61f555f5f
-- title:
--   Boolean Isoperimetry: harper case gt a ge p
-- statement:
--   In Case GT, the canonical split `p` is at most as large as `a`.
--   This is the structural half of the GT branch: if `a` is already larger than
--   the neighbourhood of `b`, then the positive canonical split of `a+b` cannot put
--   more than `a` vertices in its lower slice.  The proof uses only the earlier
--   canonical compression lemma `cascade_p_le_H_q` and monotonicity of `H`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L815-L818
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L815-L818

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

theorem BooleanIsoperimetry.harper_case_gt_a_ge_p (n : ℕ) {a b p q : ℕ}
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) : p ≤ a := by sorry
