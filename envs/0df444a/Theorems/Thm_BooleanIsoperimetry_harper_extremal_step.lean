-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_extremal_step
-- name    : BooleanIsoperimetry.harper_extremal_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:24.9148+00:00
-- url     : https://prove2.me/theorems/32ec8fab-7c8d-40cb-8831-7e1b477f6037
-- title:
--   Boolean Isoperimetry: harper extremal step
-- statement:
--   **The single remaining open step.**  The Harper/Macaulay extremal inequality at
--   level `n + 1`, derived from the *same inequality at all lower levels* (`ih`).
--
--   This is exactly `harper_extremal_n` shifted one dimension up (note the identical
--   shape: the conclusion is the cross boundary cost of the canonical cascade split
--   being minimal), so it *is* the genuine `n → n+1` inductive step of Harper's
--   vertex-isoperimetric theorem, with nothing else attached.
--
--   Compared with the original `_core` lemmas, this statement is strictly narrower:
--   it has no case hypothesis, no ordering `b ≤ a`, no positivity `1 ≤ q`, and none
--   of the eight level-`n` sub-component variables / their cascade splits / bounds.
--   It mentions only `H`, `CascadeSplit`, and `ih`, and is non-circular (it does not
--   refer to any later result such as `harper_core`, `harper_bc_min`,
--   `macaulay_optimization`, or `H_inequality_core`).
--
--   It has no elementary proof: `H (n+1)` is neither convex nor concave and the cross
--   boundary cost is not a unimodal function of the split, so the genuine
--   Kruskal–Katona / Macaulay cascade-interleaving argument is required.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1567-L1584
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1567-L1584

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

theorem BooleanIsoperimetry.harper_extremal_step (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by sorry
