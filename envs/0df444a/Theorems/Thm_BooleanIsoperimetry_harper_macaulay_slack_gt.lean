-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_slack_gt
-- name    : BooleanIsoperimetry.harper_macaulay_slack_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:27.203193+00:00
-- url     : https://prove2.me/theorems/a543eda5-62ec-443b-93be-5de428e58b3e
-- title:
--   Boolean Isoperimetry: harper macaulay slack gt
-- statement:
--   **Frankl–Füredi Case II, GT joint slack kernel (the GT corollary).**
--   Now a proved corollary of the unified kernel `harper_macaulay_joint`: in the
--   GT regime `H (n+1) b < a` the boundary `max (H (n+1) b) a` collapses to `a`
--   (`max_eq_right`).
--
--   This is the genuine *joint* slack bound; the previously-exposed split into
--   `H (n+1) q ≤ a` and `H (n+1) p ≤ H (n+1) a` is false (see the commented note
--   above), so the GT bound must keep `H (n+1) p + H (n+1) q ≤ H (n+1) a + a` intact.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1242-L1251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1242-L1251

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

theorem BooleanIsoperimetry.harper_macaulay_slack_gt (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by sorry
