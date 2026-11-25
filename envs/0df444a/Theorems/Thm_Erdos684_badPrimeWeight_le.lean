-- Prove2me | Theorems.Thm_Erdos684_badPrimeWeight_le
-- name    : Erdos684.badPrimeWeight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:41.225365+00:00
-- url     : https://prove2.me/theorems/900b96e9-847c-5572-8dd9-2337eadfe5e6
-- title:
--   Erdos684: bad Prime Weight le
-- statement:
--   The logarithmic weight of adverse primes is bounded by a short product.
--   The assertion includes `A = 0`, when the prime set is empty.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/BadPrimes.lean#L62-L103
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/BadPrimes.lean#L62-L103

module
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_BadPrimes
set_option autoImplicit false
@[expose] public section
public section
open Erdos684

theorem Erdos684.badPrimeWeight_le (n X A : ℕ) (hn : 0 < n) :
    ∑ p ∈ badPrimes n X A, Real.log (p : ℝ) ≤
      (A : ℝ) * Real.log (n + A : ℕ) := by sorry
