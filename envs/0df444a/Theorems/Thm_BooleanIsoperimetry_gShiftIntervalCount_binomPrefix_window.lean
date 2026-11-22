-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_binomPrefix_window
-- name    : BooleanIsoperimetry.gShiftIntervalCount_binomPrefix_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:33.055485+00:00
-- url     : https://prove2.me/theorems/54f27799-5b10-4977-b844-e1922cd4fe50
-- title:
--   Boolean Isoperimetry: g Shift Interval Count binom Prefix window
-- statement:
--   Whole-block value of the Macaulay shadow count between complete binomial
--   prefixes: the shadow window between `binomPrefix n r` and `binomPrefix n s`
--   counts exactly the complete Macaulay layers `r+1, …, s`.  This connects the
--   set-level shadow count to the explicit `Nat.choose` layer sizes, which is the
--   form the layer-by-layer comparison of the two shadow windows needs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L213-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L213-L219

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

theorem BooleanIsoperimetry.gShiftIntervalCount_binomPrefix_window (n r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    gShiftIntervalCount n (binomPrefix n r) (binomPrefix n s)
      = (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) := by sorry
