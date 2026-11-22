-- Prove2me | Theorems.Thm_BooleanIsoperimetry_boundaryCost_le_of_lower_interleaves_step_live
-- name    : BooleanIsoperimetry.boundaryCost_le_of_lower_interleaves_step_live
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:13.706054+00:00
-- url     : https://prove2.me/theorems/04f86565-56b2-44cf-b28e-2b0540ad5ef5
-- title:
--   Boolean Isoperimetry: boundary Cost le of lower interleaves step live
-- statement:
--   **Frankl–Füredi lowered four-block exchange step (human-proof leaf).**
--   The genuine local compression/Macaulay step in the form used by the Harper
--   induction: for the canonical cascade split `(p,q)` of `a+b` at level `n+1`,
--   in the ordered regime `b ≤ a`, with the four level-`n` cascade slice
--   decompositions of `p,q,a,b` and the lowered prefix-mass (Macaulay) domination
--   `h_lower` provided by `CascadeInterleaves.lower_succ`, and the level-`n` Harper
--   inequality `ih`, the canonical cross-boundary cost is minimal.  This carries
--   exactly the PDF's inductive inputs (within-slice optimality from
--   `ih`/`harper_extremal_n`, and cross-layer prefix-mass majorization from
--   `h_lower`).  The unordered case is recovered by `harper_macaulay_exchange_step`
--   via the symmetry of the right-hand side under swapping `a, b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L682-L780
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L682-L780

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

theorem BooleanIsoperimetry.boundaryCost_le_of_lower_interleaves_step_live
    (n p q a b p0 p1 q0 q1 a0 a1 b0 b1 : ℕ)
    (_ : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a)
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (_ : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1)
    (_ : ∀ l,
      splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by sorry
