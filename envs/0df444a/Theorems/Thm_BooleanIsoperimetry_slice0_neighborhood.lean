-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice0_neighborhood
-- name    : BooleanIsoperimetry.slice0_neighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:18:02.020868+00:00
-- url     : https://prove2.me/theorems/086a1046-0f33-4ae3-ab24-fa0e83ae311f
-- title:
--   Boolean Isoperimetry: slice0 neighborhood
-- statement:
--   The Boolean Isoperimetry construction uses the slice0 neighborhood property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L392-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L392-L432

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

theorem BooleanIsoperimetry.slice0_neighborhood {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice0 (neighborhood 1 A) = neighborhood 1 (slice0 A) ∪ slice1 A := by sorry
