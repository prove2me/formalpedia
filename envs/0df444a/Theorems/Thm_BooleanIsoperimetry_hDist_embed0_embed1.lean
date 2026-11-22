-- Prove2me | Theorems.Thm_BooleanIsoperimetry_hDist_embed0_embed1
-- name    : BooleanIsoperimetry.hDist_embed0_embed1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:53.529798+00:00
-- url     : https://prove2.me/theorems/d3871e34-b21a-4b9b-b4e4-eba9ad2d4b8d
-- title:
--   Boolean Isoperimetry: h Dist embed0 embed1
-- statement:
--   The Boolean Isoperimetry construction uses the h Dist embed0 embed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L376-L390
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cube.lean#L376-L390

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

theorem BooleanIsoperimetry.hDist_embed0_embed1 {n : ℕ} (x y : Cube n) :
    hDist (embed0 x) (embed1 y) = hDist x y + 1 := by sorry
