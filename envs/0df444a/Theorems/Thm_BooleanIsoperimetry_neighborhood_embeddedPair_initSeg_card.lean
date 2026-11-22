-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_embeddedPair_initSeg_card
-- name    : BooleanIsoperimetry.neighborhood_embeddedPair_initSeg_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:39.495405+00:00
-- url     : https://prove2.me/theorems/ec80194a-cd46-4d7e-b79e-1d328adcb869
-- title:
--   Boolean Isoperimetry: neighborhood embedded Pair init Seg card
-- statement:
--   For canonical initial segments the literal embedded-neighborhood cardinality
--   also evaluates to the scalar max expression, because all four slice families are
--   nested initial segments.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L185-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L185-L191

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

theorem BooleanIsoperimetry.neighborhood_embeddedPair_initSeg_card {N a b : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (embeddedPair N (simplicialInitSeg N a) (simplicialInitSeg N b))).card =
      max (H N a) b + max (H N b) a := by sorry
