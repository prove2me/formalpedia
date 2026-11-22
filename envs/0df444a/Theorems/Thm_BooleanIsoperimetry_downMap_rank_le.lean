-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downMap_rank_le
-- name    : BooleanIsoperimetry.downMap_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:41.686293+00:00
-- url     : https://prove2.me/theorems/8937eba2-ba02-4290-b9ad-fe1ec8b8ff43
-- title:
--   Boolean Isoperimetry: down Map rank le
-- statement:
--   The Down map never increases simplicial rank.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L482-L487
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L482-L487

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.downMap_rank_le {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    rank (downMap i A x) ≤ rank x := by sorry
