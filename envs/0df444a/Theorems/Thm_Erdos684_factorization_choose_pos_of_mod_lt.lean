-- Prove2me | Theorems.Thm_Erdos684_factorization_choose_pos_of_mod_lt
-- name    : Erdos684.factorization_choose_pos_of_mod_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:45.486299+00:00
-- url     : https://prove2.me/theorems/e1ab8541-89e1-4ebf-9765-df6eb0517752
-- title:
--   Erdos684: factorization choose pos of mod lt
-- statement:
--   A first-level carry forces a positive prime exponent in the binomial coefficient.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L56-L72
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L56-L72

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

theorem Erdos684.factorization_choose_pos_of_mod_lt {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) :
    0 < (n.choose k).factorization p := by sorry
