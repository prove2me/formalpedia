-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_ge_binomPrefix_window_of_endpoints
-- name    : BooleanIsoperimetry.gShiftIntervalCount_ge_binomPrefix_window_of_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:11.824614+00:00
-- url     : https://prove2.me/theorems/2f1e344b-3469-4b10-95d8-759b63a00604
-- title:
--   Boolean Isoperimetry: g Shift Interval Count ge binom Prefix window of endpoints
-- statement:
--   **Lower block bound (dual of `gShiftIntervalCount_le_binomPrefix_window_of_endpoints`).**
--   If a shadow window `[lo, hi)` *contains* the complete binomial prefix block
--   `[binomPrefix n r, binomPrefix n s)` (that is, `lo ≤ binomPrefix n r` and
--   `binomPrefix n s ≤ hi`), then its shadow count is at least the complete-layer
--   block sum `∑_{i = r+1}^{s} C(n, i)`.
--
--   This is the missing companion of the existing upper bound: together they let a
--   Macaulay shadow comparison *lower-bound the upper window* and *upper-bound the
--   lower window* by explicit `Nat.choose` layer sums.  It is the reusable
--   accounting helper named in Aristotle's Cycle 1 plan, and is the set-level form
--   of "a window that swallows whole layers counts at least those layers".
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L262-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L262-L278

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

theorem BooleanIsoperimetry.gShiftIntervalCount_ge_binomPrefix_window_of_endpoints
    (n r s lo hi : ℕ)
    (hr : 1 ≤ r) (hrs : r ≤ s)
    (hlo : lo ≤ binomPrefix n r)
    (hhi : binomPrefix n s ≤ hi) :
    (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) ≤
      gShiftIntervalCount n lo hi := by sorry
