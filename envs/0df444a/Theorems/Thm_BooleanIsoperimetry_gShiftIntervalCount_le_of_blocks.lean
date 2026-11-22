-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_le_of_blocks
-- name    : BooleanIsoperimetry.gShiftIntervalCount_le_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:34.509281+00:00
-- url     : https://prove2.me/theorems/973b3962-2cb5-4905-ad2a-b7dd17a1ffad
-- title:
--   Boolean Isoperimetry: g Shift Interval Count le of blocks
-- statement:
--   **Block-domination ⇒ shadow-window domination.**
--   Two shadow windows compared through their enclosing/enclosed complete binomial
--   blocks.  If the *lower* window `[lo₁, hi₁)` is enclosed in the layer band
--   `[r₁, s₁]` (so it is upper-bounded by the block sum over `r₁+1 .. s₁`) and the
--   *upper* window `[lo₂, hi₂)` swallows the layer band `[r₂, s₂]` (so it is
--   lower-bounded by the block sum over `r₂+1 .. s₂`), and the first block sum is no
--   larger than the second, then the lower window's shadow count is no larger than
--   the upper window's.
--
--   This is the reusable whole-block comparison engine that the Frankl–Füredi /
--   Macaulay window comparison (`harper_macaulay_LE_sum`, `harper_macaulay_GT_sum`)
--   reduces to once the partial-layer boundary pieces of each window have been
--   absorbed into the enclosing layer band.  It is `ih`-free and purely `Nat.choose`
--   arithmetic at the block level, isolating exactly the layer-index bookkeeping from
--   the set-level shadow content.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L297-L311
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L297-L311

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

theorem BooleanIsoperimetry.gShiftIntervalCount_le_of_blocks
    (n r₁ s₁ r₂ s₂ lo₁ hi₁ lo₂ hi₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hrs₁ : r₁ ≤ s₁)
    (hr₂ : 1 ≤ r₂) (hrs₂ : r₂ ≤ s₂)
    (hlo₁ : binomPrefix n r₁ ≤ lo₁) (hhi₁ : hi₁ ≤ binomPrefix n s₁)
    (hlo₂ : lo₂ ≤ binomPrefix n r₂) (hhi₂ : binomPrefix n s₂ ≤ hi₂)
    (hblock :
      (Finset.Ico (r₁ + 1) (s₁ + 1)).sum (fun i => Nat.choose n i) ≤
        (Finset.Ico (r₂ + 1) (s₂ + 1)).sum (fun i => Nat.choose n i)) :
    gShiftIntervalCount n lo₁ hi₁ ≤ gShiftIntervalCount n lo₂ hi₂ := by sorry
