-- Prove2me | Theorems.Thm_BooleanIsoperimetry_sdiff_card_lt_sdiff_card_of_card_lt
-- name    : BooleanIsoperimetry.sdiff_card_lt_sdiff_card_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:12.952813+00:00
-- url     : https://prove2.me/theorems/d3234fc9-9e22-43d0-89e8-86253e4ad785
-- title:
--   Boolean Isoperimetry: sdiff card lt sdiff card of card lt
-- statement:
--   Cardinality comparison for the block replacement associated to
--   `T.card < S.card`: the inserted block `T \ S` is strictly smaller than the
--   removed block `S \ T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1424-L1431
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1424-L1431

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.sdiff_card_lt_sdiff_card_of_card_lt {N : ℕ} {S T : Cube N}
    (hcard : T.card < S.card) : (T \ S).card < (S \ T).card := by sorry
