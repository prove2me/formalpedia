-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_step_le_sum_form
-- name    : BooleanIsoperimetry.harper_step_le_sum_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:21.372542+00:00
-- url     : https://prove2.me/theorems/6072b30b-ece8-4467-a32a-ea1c078ff5d5
-- title:
--   Boolean Isoperimetry: harper step le sum form
-- statement:
--   **Frankl–Füredi Case I, sum form.**
--   In the LE regime `a ≤ H (n+1) b`, the max-form boundary cost collapses to the
--   plain sum `H (n+1) a + H (n+1) b`.  This lemma is now a proved reduction to
--   the canonical-sum core `harper_step_le_canonical_sum`: after choosing the
--   canonical split `(p,q)` of `a+b` and dispatching the degenerate `q = 0` branch,
--   the positive branch rewrites `H (n+2) (a+b)` to `H(n+1)p + H(n+1)q` and applies
--   the core.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1360-L1396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1360-L1396

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

theorem BooleanIsoperimetry.harper_step_le_sum_form (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 2) (a + b) ≤ H (n + 1) a + H (n + 1) b := by sorry
