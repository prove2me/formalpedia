-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_shadow_gt
-- name    : BooleanIsoperimetry.harper_macaulay_shadow_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:08.532142+00:00
-- url     : https://prove2.me/theorems/f27870c0-a9d8-4812-927f-fd07a22941cc
-- title:
--   Boolean Isoperimetry: harper macaulay shadow gt
-- statement:
--   GT Macaulay shadow slack comparison (PDF-faithful shadow-count form).  Now a
--   proved corollary of the joint slack kernel `harper_macaulay_slack_gt`:
--   `harper_gt_split_between` supplies `b ≤ q ≤ p ≤ a`, the shadow windows rewrite to
--   `H` differences, and the goal follows by arithmetic (`H_mono` plus `omega`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1259-L1274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1259-L1274

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

theorem BooleanIsoperimetry.harper_macaulay_shadow_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : H (n + 1) b < a) (hq_pos : 1 ≤ q) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - H (n + 1) b) := by sorry
