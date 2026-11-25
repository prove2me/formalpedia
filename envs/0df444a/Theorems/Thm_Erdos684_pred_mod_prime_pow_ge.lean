-- Prove2me | Theorems.Thm_Erdos684_pred_mod_prime_pow_ge
-- name    : Erdos684.pred_mod_prime_pow_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:05.497374+00:00
-- url     : https://prove2.me/theorems/94225eac-9070-413d-848b-d17208bed8f1
-- title:
--   Erdos684: pred mod prime pow ge
-- statement:
--   A sufficiently large prime power divisor prevents all carries for a small lower index.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L107-L121
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L107-L121

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

theorem Erdos684.pred_mod_prime_pow_ge {M K p e : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hlarge : K < p ^ e) (hdiv : p ^ e ∣ M) {k : ℕ} (hk : k ≤ K) (i : ℕ) :
    k % p ^ i ≤ (M - 1) % p ^ i := by sorry
