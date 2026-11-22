-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_extremal_step_nested_pos
-- name    : BooleanIsoperimetry.harper_extremal_step_nested_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:29.23518+00:00
-- url     : https://prove2.me/theorems/324f5b1e-7dec-43a5-a6ca-3f89e9cf3203
-- title:
--   Boolean Isoperimetry: harper extremal step nested pos
-- statement:
--   The four-block Frankl-Furedi profile bridge, now a proved consequence of
--   the pure-`H` kernel `harper_step_total`.  Using
--   `pairedCascadeBoundary_pos_eq_H_succ`, the four-block boundary on the left is
--   exactly `H (n+2) (a+b)`, and the conclusion is then `harper_step_total`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1481-L1509
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1481-L1509

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

theorem BooleanIsoperimetry.harper_extremal_step_nested_pos (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by sorry
