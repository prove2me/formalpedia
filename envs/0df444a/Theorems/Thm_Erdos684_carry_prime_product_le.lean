-- Prove2me | Theorems.Thm_Erdos684_carry_prime_product_le
-- name    : Erdos684.carry_prime_product_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:48:16.880108+00:00
-- url     : https://prove2.me/theorems/236c6b89-4999-4c7c-ac3b-66055464b04e
-- title:
--   Erdos684: carry prime product le
-- statement:
--   Multiplying primes with a first-level carry gives a lower bound on the small-prime part.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L84-L98
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L84-L98

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
set_option autoImplicit false
@[expose] public section
public section
open Erdos684

theorem Erdos684.carry_prime_product_le (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ (Nat.primesLE k).filter (fun p => n % p < k % p), p) ≤
      smallPrimePart n k := by sorry
