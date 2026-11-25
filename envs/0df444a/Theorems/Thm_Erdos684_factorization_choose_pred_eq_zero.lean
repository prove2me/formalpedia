-- Prove2me | Theorems.Thm_Erdos684_factorization_choose_pred_eq_zero
-- name    : Erdos684.factorization_choose_pred_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:28.857797+00:00
-- url     : https://prove2.me/theorems/c4166e45-498c-4334-b29d-51df9be86a0a
-- title:
--   Erdos684: factorization choose pred eq zero
-- statement:
--   A prime power divisor exceeding the lower index forces zero binomial valuation.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L137-L148
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L137-L148

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

theorem Erdos684.factorization_choose_pred_eq_zero {M K p e : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hlarge : K < p ^ e) (hdiv : p ^ e ∣ M) {k : ℕ} (hk : k ≤ K) :
    ((M - 1).choose k).factorization p = 0 := by sorry
