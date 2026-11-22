-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_full
-- name    : BooleanIsoperimetry.H_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:24.214811+00:00
-- url     : https://prove2.me/theorems/a4be4ecc-b2be-40cd-b7bb-0b702e171d58
-- title:
--   Boolean Isoperimetry: H full
-- statement:
--   The Boolean Isoperimetry construction uses the H full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L519-L520
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L519-L520

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

theorem BooleanIsoperimetry.H_full (n : ℕ) : H n (2 ^ n) = 2 ^ n := by sorry
