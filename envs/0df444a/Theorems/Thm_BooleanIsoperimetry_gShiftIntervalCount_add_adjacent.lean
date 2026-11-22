-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_add_adjacent
-- name    : BooleanIsoperimetry.gShiftIntervalCount_add_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:31.536796+00:00
-- url     : https://prove2.me/theorems/388b4740-7812-4e75-a793-0d70bc0500a7
-- title:
--   Boolean Isoperimetry: g Shift Interval Count add adjacent
-- statement:
--   Window additivity for the Macaulay shadow count `gShiftIntervalCount`:
--   adjacent rank windows `[lo, mid)` and `[mid, hi)` add to `[lo, hi)`.  A reusable
--   block-decomposition tool for splitting shadow windows along layer boundaries.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L197-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L197-L206

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

theorem BooleanIsoperimetry.gShiftIntervalCount_add_adjacent (n lo mid hi : ℕ)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    gShiftIntervalCount n lo mid + gShiftIntervalCount n mid hi
      = gShiftIntervalCount n lo hi := by sorry
