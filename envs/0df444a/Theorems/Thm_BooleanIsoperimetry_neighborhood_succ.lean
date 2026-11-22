-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_succ
-- name    : BooleanIsoperimetry.neighborhood_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:28.640897+00:00
-- url     : https://prove2.me/theorems/fd995067-6045-4a33-a0f5-ede5330a5e69
-- title:
--   Boolean Isoperimetry: neighborhood succ
-- statement:
--   The Boolean Isoperimetry construction uses the neighborhood succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L479-L483
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L479-L483

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

theorem BooleanIsoperimetry.neighborhood_succ {n : ℕ} (A : Finset (Cube (n + 1))) :
    (neighborhood 1 A).card =
    (neighborhood 1 (slice0 A) ∪ slice1 A).card +
    (neighborhood 1 (slice1 A) ∪ slice0 A).card := by sorry
