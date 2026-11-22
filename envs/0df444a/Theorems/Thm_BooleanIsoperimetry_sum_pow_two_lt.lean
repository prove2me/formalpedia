-- Prove2me | Theorems.Thm_BooleanIsoperimetry_sum_pow_two_lt
-- name    : BooleanIsoperimetry.sum_pow_two_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:27:07.048804+00:00
-- url     : https://prove2.me/theorems/479f9cb5-a1bc-45c8-b21f-dc65d6cf79c6
-- title:
--   Boolean Isoperimetry: sum pow two lt
-- statement:
--   The Boolean Isoperimetry construction uses the sum pow two lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L65-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L65-L66

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.sum_pow_two_lt (n : ℕ) : (∑ i ∈ Finset.range n, 2^i) < 2^n := by sorry
