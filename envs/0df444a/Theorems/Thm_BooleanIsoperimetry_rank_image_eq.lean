-- Prove2me | Theorems.Thm_BooleanIsoperimetry_rank_image_eq
-- name    : BooleanIsoperimetry.rank_image_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:36.688106+00:00
-- url     : https://prove2.me/theorems/a3544614-b910-41ba-97ff-9b0670f355f4
-- title:
--   Boolean Isoperimetry: rank image eq
-- statement:
--   The Boolean Isoperimetry construction uses the rank image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L262-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L262-L266

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

theorem BooleanIsoperimetry.rank_image_eq {n : ℕ} :
    Finset.univ.image (@rank n) = Finset.range (2 ^ n) := by sorry
