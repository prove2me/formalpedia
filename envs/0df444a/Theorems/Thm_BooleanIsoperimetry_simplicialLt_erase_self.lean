-- Prove2me | Theorems.Thm_BooleanIsoperimetry_simplicialLt_erase_self
-- name    : BooleanIsoperimetry.simplicialLt_erase_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:28.435896+00:00
-- url     : https://prove2.me/theorems/86176b28-d13e-42df-acff-f4d06fd46af1
-- title:
--   Boolean Isoperimetry: simplicial Lt erase self
-- statement:
--   Erasing a present coordinate is a strictly earlier simplicial vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L473-L479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L473-L479

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

theorem BooleanIsoperimetry.simplicialLt_erase_self {N : ℕ} {i : Fin N} {x : Cube N} (hi : i ∈ x) :
    simplicialLt (x.erase i) x := by sorry
