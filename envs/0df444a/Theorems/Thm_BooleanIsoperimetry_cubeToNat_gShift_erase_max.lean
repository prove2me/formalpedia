-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cubeToNat_gShift_erase_max
-- name    : BooleanIsoperimetry.cubeToNat_gShift_erase_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:52.431195+00:00
-- url     : https://prove2.me/theorems/a4c5c646-eb06-4663-a698-3ea96c56a554
-- title:
--   Boolean Isoperimetry: cube To Nat g Shift erase max
-- statement:
--   The Boolean Isoperimetry construction uses the cube To Nat g Shift erase max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L675-L706
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L675-L706

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

theorem BooleanIsoperimetry.cubeToNat_gShift_erase_max {n : ℕ} {x : Cube n} (hx : x.Nonempty) (h2 : 2 ≤ x.card) :
    cubeToNat (gShift x) =
      cubeToNat (gShift (x.erase (x.max' hx))) + 2 ^ ((x.max' hx : ℕ)) := by sorry
