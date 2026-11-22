-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_macaulayShadowWeight_sum
-- name    : BooleanIsoperimetry.gShiftIntervalCount_eq_macaulayShadowWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:52.362213+00:00
-- url     : https://prove2.me/theorems/587f439c-f7c4-424d-a386-f08e5b682049
-- title:
--   Boolean Isoperimetry: g Shift Interval Count eq macaulay Shadow Weight sum
-- statement:
--   Exact vertex-weight form of a Macaulay shadow window.  This is the same window
--   count as `gShiftIntervalCount`, but with each rank vertex weighted by its
--   explicit `gShift`-fibre size (`macaulayShadowWeight`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L79-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L79-L85

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

theorem BooleanIsoperimetry.gShiftIntervalCount_eq_macaulayShadowWeight_sum
    (n lo hi : ℕ) (hlohi : lo ≤ hi) (hhi : hi ≤ 2 ^ n) :
    gShiftIntervalCount n lo hi =
      ∑ w ∈ (Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)),
        macaulayShadowWeight w := by sorry
