-- Prove2me | Theorems.Thm_CriticalPortraits_Cycle_Q_succ
-- name    : CriticalPortraits.Cycle.Q_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:41.549572+00:00
-- url     : https://prove2.me/theorems/896e55d6-1131-496e-ac90-41cda4699b0a
-- title:
--   Cycle: Q succ
-- statement:
--   The Cycle construction uses the Q succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L41-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L41-L42

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

theorem CriticalPortraits.Cycle.Q_succ (a : ℕ → ℤ) (k : ℕ) : Q a (k + 1) = Q a k + a k := by sorry
