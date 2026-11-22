-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_le_binomPrefix_window_of_endpoints
-- name    : BooleanIsoperimetry.gShiftIntervalCount_le_binomPrefix_window_of_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:10.828864+00:00
-- url     : https://prove2.me/theorems/39ab51a2-f876-412f-8f3d-d807b13d0f2e
-- title:
--   Boolean Isoperimetry: g Shift Interval Count le binom Prefix window of endpoints
-- statement:
--   The Boolean Isoperimetry construction uses the g Shift Interval Count le binom Prefix window of endpoints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L221-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L221-L247

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

theorem BooleanIsoperimetry.gShiftIntervalCount_le_binomPrefix_window_of_endpoints
    (n r s lo hi : ℕ)
    (hr : 1 ≤ r) (hrs : r ≤ s)
    (hlo : binomPrefix n r ≤ lo)
    (hhi : hi ≤ binomPrefix n s) :
    gShiftIntervalCount n lo hi ≤
      (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by sorry
