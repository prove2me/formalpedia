-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_initialSlicePair_card
-- name    : BooleanIsoperimetry.neighborhood_initialSlicePair_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:06.58336+00:00
-- url     : https://prove2.me/theorems/11b1be52-429c-42ec-9250-789401f37d0b
-- title:
--   Boolean Isoperimetry: neighborhood initial Slice Pair card
-- statement:
--   The Boolean Isoperimetry construction uses the neighborhood initial Slice Pair card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L670-L676
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L670-L676

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

theorem BooleanIsoperimetry.neighborhood_initialSlicePair_card {N a b : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (initialSlicePair N a b)).card =
      max (H N a) b + max (H N b) a := by sorry
