-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_step_le_canonical_sum
-- name    : BooleanIsoperimetry.harper_step_le_canonical_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:20.688697+00:00
-- url     : https://prove2.me/theorems/5b498038-9f37-4f3a-93dc-fa90ef4b729a
-- title:
--   Boolean Isoperimetry: harper step le canonical sum
-- statement:
--   **Frankl–Füredi Case I, canonical-sum core.**
--   For the canonical cascade split `(p, q)` of `a + b` at dimension `n + 1`, in the
--   LE regime `b ≤ a ≤ H (n+1) b`, the canonical boundary sum `H(n+1)p + H(n+1)q`
--   is bounded by the arbitrary-split boundary sum `H(n+1)a + H(n+1)b`.
--
--   This is the genuine max-free Macaulay heart of the LE case.  It is strictly
--   narrower than `harper_step_total`: it adds the ordering hypothesis `b ≤ a` and
--   the case hypothesis `a ≤ H (n+1) b`, fixes the canonical split, and has the two
--   outer `max`s already collapsed.  It mentions only `H`, `CascadeSplit`, and the
--   level-`n` induction hypothesis `ih`, and is non-circular.
--
--   NOTE (cycle37.aristotle).  This replaces the previous leaf
--   `harper_step_le_window_shift`, which asserted the endpoint order `a ≤ p` together
--   with a `gShiftIntervalCount` window inequality.  An exact computational model of
--   `H` via the cascade recursion shows `a ≤ p` is **false** in the LE regime (176
--   counterexamples for `n ≤ 4`, smallest `n = 1, a = 4, b = 2` with `(p,q)=(3,3)`):
--   the canonical split can place *less* than `a` in its lower slice, so the windows
--   `[a,p)` and `[q,b)` are not nested as that lemma required.  The *sum* form proved
--   here is true (0 counterexamples for `n ≤ 6`) and is the correct LE leaf.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1297-L1316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1297-L1316

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

theorem BooleanIsoperimetry.harper_step_le_canonical_sum (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by sorry
