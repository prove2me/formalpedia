-- Prove2me | Theorems.Thm_CriticalPortraits_Cycle_Q_periodic
-- name    : CriticalPortraits.Cycle.Q_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:36.100771+00:00
-- url     : https://prove2.me/theorems/869c1c7d-4d9d-459b-b0fa-b65de406864a
-- title:
--   Cycle: Q periodic
-- statement:
--   Periodicity of the partial sums: `Q (k+n) = Q k + (period sum)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L57-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/CycleLemma.lean#L57-L61

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

theorem CriticalPortraits.Cycle.Q_periodic (a : ℕ → ℤ) (hper : ∀ k, a (k + n) = a k) (hsum : Q a n = 1)
    (k : ℕ) : Q a (k + n) = Q a k + 1 := by sorry
