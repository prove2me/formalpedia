-- Prove2me | Theorems.Thm_CriticalPortraits_Cycle_cycle_lemma
-- name    : CriticalPortraits.Cycle.cycle_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:36.071181+00:00
-- url     : https://prove2.me/theorems/a29e90e6-61aa-439f-80b3-f9d7ae5ab7b7
-- title:
--   Cycle: cycle lemma
-- statement:
--   **The cycle lemma (Raney), sum = 1.** For a period-`n` integer sequence with period-sum `1`,
--       exactly one shift `i ∈ [0,n)` is good. The witness is the *last* argmin of `Q` over `[0,n)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L69-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L69-L110

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

theorem CriticalPortraits.Cycle.cycle_lemma (a : ℕ → ℤ) (hn : 0 < n) (hper : ∀ k, a (k + n) = a k)
    (hsum : Q a n = 1) : ∃! i, i < n ∧ Good n a i := by sorry
