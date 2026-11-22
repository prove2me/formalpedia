-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_window_sum_of_le
-- name    : BooleanIsoperimetry.H_window_sum_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:56.708851+00:00
-- url     : https://prove2.me/theorems/f0fd3a63-a52f-4242-b1fe-35378bdcdf2a
-- title:
--   Boolean Isoperimetry: H window sum of le
-- statement:
--   The Boolean Isoperimetry construction uses the H window sum of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L36-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L36-L41

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

theorem BooleanIsoperimetry.H_window_sum_of_le (n lo hi : ℕ) (hlohi : lo ≤ hi) :
    H n hi = H n lo + ∑ i ∈ Finset.Ico lo hi, HIncrement n i := by sorry
