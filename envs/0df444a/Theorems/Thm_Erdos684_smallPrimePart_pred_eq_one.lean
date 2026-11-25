-- Prove2me | Theorems.Thm_Erdos684_smallPrimePart_pred_eq_one
-- name    : Erdos684.smallPrimePart_pred_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:51.246711+00:00
-- url     : https://prove2.me/theorems/ca26ca5a-a079-4dcc-926a-fc458c7eff5c
-- title:
--   Erdos684: small Prime Part pred eq one
-- statement:
--   If each small prime has a divisor power exceeding `K`, every small-prime part up to `K` is one.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L151-L158
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L151-L158

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

theorem Erdos684.smallPrimePart_pred_eq_one {M K : ℕ} (hM : 0 < M)
    (hpowers : ∀ p, p.Prime → p ≤ K → ∃ e, K < p ^ e ∧ p ^ e ∣ M)
    {k : ℕ} (hk : k ≤ K) : smallPrimePart (M - 1) k = 1 := by sorry
