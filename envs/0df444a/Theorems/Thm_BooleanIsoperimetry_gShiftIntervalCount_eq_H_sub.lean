-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_H_sub
-- name    : BooleanIsoperimetry.gShiftIntervalCount_eq_H_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:08.784146+00:00
-- url     : https://prove2.me/theorems/c0e791bf-e858-4dbe-816c-b3972a5f2a47
-- title:
--   Boolean Isoperimetry: g Shift Interval Count eq H sub
-- statement:
--   The Boolean Isoperimetry construction uses the g Shift Interval Count eq H sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L43-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L43-L65

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

theorem BooleanIsoperimetry.gShiftIntervalCount_eq_H_sub (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    gShiftIntervalCount n lo hi = H n hi - H n lo := by sorry
