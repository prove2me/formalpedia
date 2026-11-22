-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_le_of_layer
-- name    : BooleanIsoperimetry.gShiftIntervalCount_le_of_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:42.661802+00:00
-- url     : https://prove2.me/theorems/3b24e507-a98a-45be-b29e-31252afd30af
-- title:
--   Boolean Isoperimetry: g Shift Interval Count le of layer
-- statement:
--   **Single-layer shadow-window bound.**  A length-`L` shadow window contained in
--   a single Macaulay layer `r` has shadow count at most `L * (n - r)`.  This is the
--   set-level form of `HIncrement_window_le_of_layer`: it is the reusable upper bound
--   for the *upper* shadow window of the Frankl–Füredi/Macaulay comparison whenever
--   that window stays inside one cardinality band (which, computationally, is exactly
--   the regime of the reversed-orientation leaf `harper_macaulay_reversed`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L319-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L319-L323

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

theorem BooleanIsoperimetry.gShiftIntervalCount_le_of_layer {n r a L : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ a) (hhi : a + L ≤ binomPrefix n (r + 1)) :
    gShiftIntervalCount n a (a + L) ≤ L * (n - r) := by sorry
