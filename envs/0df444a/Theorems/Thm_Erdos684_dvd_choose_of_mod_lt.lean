-- Prove2me | Theorems.Thm_Erdos684_dvd_choose_of_mod_lt
-- name    : Erdos684.dvd_choose_of_mod_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:48:07.040593+00:00
-- url     : https://prove2.me/theorems/b6b0e238-8615-56ac-b561-1feb02603148
-- title:
--   Erdos684: dvd choose of mod lt
-- statement:
--   The Erdos684 construction uses the dvd choose of mod lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L79-L81
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L79-L81

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

theorem Erdos684.dvd_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) : p ∣ n.choose k := by sorry
