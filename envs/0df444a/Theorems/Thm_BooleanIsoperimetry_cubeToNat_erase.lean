-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cubeToNat_erase
-- name    : BooleanIsoperimetry.cubeToNat_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:39.089352+00:00
-- url     : https://prove2.me/theorems/7edbacb9-dfb3-4936-97fa-67f08b3ac52d
-- title:
--   Boolean Isoperimetry: cube To Nat erase
-- statement:
--   The Boolean Isoperimetry construction uses the cube To Nat erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L642-L644
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L642-L644

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

theorem BooleanIsoperimetry.cubeToNat_erase {n : ℕ} {x : Cube n} {a : Fin n} (ha : a ∈ x) :
    cubeToNat x = cubeToNat (x.erase a) + 2 ^ (a : ℕ) := by sorry
