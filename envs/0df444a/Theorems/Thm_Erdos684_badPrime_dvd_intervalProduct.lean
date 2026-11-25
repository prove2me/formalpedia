-- Prove2me | Theorems.Thm_Erdos684_badPrime_dvd_intervalProduct
-- name    : Erdos684.badPrime_dvd_intervalProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:44.3078+00:00
-- url     : https://prove2.me/theorems/49d6d0dc-abe3-4bf8-af80-9809972270df
-- title:
--   Erdos684: bad Prime dvd interval Product
-- statement:
--   Each adverse prime divides the product of the next `A` positive terms.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/BadPrimes.lean#L49-L58
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/BadPrimes.lean#L49-L58

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

theorem Erdos684.badPrime_dvd_intervalProduct {n X A p : ℕ}
    (hp : p ∈ badPrimes n X A) :
    p ∣ ∏ j ∈ Finset.Icc 1 A, (n + j) := by sorry
