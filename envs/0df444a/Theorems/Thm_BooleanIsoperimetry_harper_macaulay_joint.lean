-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_joint
-- name    : BooleanIsoperimetry.harper_macaulay_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:37.432567+00:00
-- url     : https://prove2.me/theorems/5f7ed1a2-076c-4d4f-abfb-ca61ddecbef4
-- title:
--   Boolean Isoperimetry: harper macaulay joint
-- statement:
--   **Frankl–Füredi joint Macaulay kernel — the single unified leaf (LE ∪ GT).**
--   For the canonical cascade split `(p, q)` of `a + b` at level `n + 1` (so `(p,q)`
--   is the split of `a + b` in the `(n+2)`-cube, while the boundary values live in
--   the `(n+1)`-cube), in the ordered regime `b ≤ a`, the canonical boundary sum
--   `H (n+1) p + H (n+1) q` is bounded by the **arbitrary-split boundary functional**
--   `H (n+1) a + max (H (n+1) b) a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1195-L1213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1195-L1213

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

theorem BooleanIsoperimetry.harper_macaulay_joint (n : ℕ) {a b p q : ℕ}
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + max (H (n + 1) b) a := by sorry
