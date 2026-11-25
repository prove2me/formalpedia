-- Prove2me | Theorems.Thm_Erdos684_one_le_factorization_choose_of_mod_lt
-- name    : Erdos684.one_le_factorization_choose_of_mod_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:58.043806+00:00
-- url     : https://prove2.me/theorems/9003775a-1b07-4ea1-a4b2-8370449e109b
-- title:
--   Erdos684: one le factorization choose of mod lt
-- statement:
--   The Erdos684 construction uses the one le factorization choose of mod lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L74-L77
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L74-L77

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

theorem Erdos684.one_le_factorization_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) :
    1 ≤ (n.choose k).factorization p := by sorry
