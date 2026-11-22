-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_macaulay_exchange_step
-- name    : BooleanIsoperimetry.harper_macaulay_exchange_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:30.027351+00:00
-- url     : https://prove2.me/theorems/2471d969-97f6-4fae-8fe9-5f512b148ee6
-- title:
--   Boolean Isoperimetry: harper macaulay exchange step
-- statement:
--   **Frankl–Füredi / Macaulay extremal step (max-form).**
--   For the canonical cascade split `(p,q)` of `a+b` at level `n+1`, the canonical
--   cross-boundary cost is minimal.  This is now a sorry-free consequence of the
--   single human-proof leaf `boundaryCost_le_of_lower_interleaves_step_live`: choose
--   the four level-`n` cascade slice decompositions of `p,q,a,b` via
--   `exists_cascade_split`, obtain the lowered prefix-mass domination from
--   `canonicalSplit_interleaves` and `CascadeInterleaves.lower_succ`, and apply the
--   leaf.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L790-L815
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L790-L815

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

theorem BooleanIsoperimetry.harper_macaulay_exchange_step (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by sorry
