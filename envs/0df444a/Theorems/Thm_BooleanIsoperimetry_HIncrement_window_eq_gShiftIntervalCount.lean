-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_window_eq_gShiftIntervalCount
-- name    : BooleanIsoperimetry.HIncrement_window_eq_gShiftIntervalCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:13.598806+00:00
-- url     : https://prove2.me/theorems/7b6bb20d-e41e-4dc6-8f3c-1cd032370a60
-- title:
--   Boolean Isoperimetry: HIncrement window eq g Shift Interval Count
-- statement:
--   The Boolean Isoperimetry construction uses the HIncrement window eq g Shift Interval Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L67-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L67-L72

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

theorem BooleanIsoperimetry.HIncrement_window_eq_gShiftIntervalCount (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi, HIncrement n i) = gShiftIntervalCount n lo hi := by sorry
