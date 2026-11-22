-- Prove2me | Theorems.Thm_BooleanIsoperimetry_embed1_cubeToNat
-- name    : BooleanIsoperimetry.embed1_cubeToNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:59.594156+00:00
-- url     : https://prove2.me/theorems/bde9041c-3bf6-4b12-a294-480abe764910
-- title:
--   Boolean Isoperimetry: embed1 cube To Nat
-- statement:
--   The Boolean Isoperimetry construction uses the embed1 cube To Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L855-L867
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L855-L867

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

theorem BooleanIsoperimetry.embed1_cubeToNat {n : ℕ} (x : Cube n) : cubeToNat (embed1 x) = cubeToNat x + 2 ^ n := by sorry
