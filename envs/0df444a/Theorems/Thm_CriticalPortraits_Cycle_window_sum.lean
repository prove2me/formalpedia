-- Prove2me | Theorems.Thm_CriticalPortraits_Cycle_window_sum
-- name    : CriticalPortraits.Cycle.window_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:33.727181+00:00
-- url     : https://prove2.me/theorems/df1f5fbf-ed09-45b9-a595-d2b63b0537ce
-- title:
--   Cycle: window sum
-- statement:
--   A window of length `n` of a period-`n` sequence sums to the period sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L45-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L45-L54

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits CriticalPortraits.Cycle
variable {n : ℕ}

theorem CriticalPortraits.Cycle.window_sum (a : ℕ → ℤ) (hper : ∀ k, a (k + n) = a k)
    (k : ℕ) : Q a (k + n) - Q a k = Q a n - Q a 0 := by sorry
