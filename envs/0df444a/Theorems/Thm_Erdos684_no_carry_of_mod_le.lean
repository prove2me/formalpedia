-- Prove2me | Theorems.Thm_Erdos684_no_carry_of_mod_le
-- name    : Erdos684.no_carry_of_mod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:09.524831+00:00
-- url     : https://prove2.me/theorems/db7dc448-76ff-48aa-98a1-279b64d67609
-- title:
--   Erdos684: no carry of mod le
-- statement:
--   A residue inequality excludes a carry when a natural number is split into two summands.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L124-L134
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L124-L134

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

theorem Erdos684.no_carry_of_mod_le {n k q : ℕ} (hkn : k ≤ n) (hq : 0 < q)
    (hmod : k % q ≤ n % q) : k % q + (n - k) % q < q := by sorry
