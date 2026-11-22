-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_step_gt
-- name    : BooleanIsoperimetry.harper_step_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:20.890287+00:00
-- url     : https://prove2.me/theorems/d8d6587b-00b8-43ab-b5d5-c52c4e44acf4
-- title:
--   Boolean Isoperimetry: harper step gt
-- statement:
--   **Frankl–Füredi Case II (the GT regime).**  Under `b ≤ a` and `H (n+1) b < a`,
--   the boundary cost `boundaryCostH (n+1) a b` collapses to `H (n+1) a + a`.  This
--   is the max-free combinatorial heart of Harper's `n → n+1` step in the GT regime.
--
--   It is strictly narrower than `harper_step_total` (adds `b ≤ a` and the case
--   hypothesis `H (n+1) b < a`, with the outer `max`s eliminated), mentions only
--   `H` and `ih`, and is non-circular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1415-L1442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1415-L1442

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

theorem BooleanIsoperimetry.harper_step_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 2) (a + b) ≤ H (n + 1) a + a := by sorry
