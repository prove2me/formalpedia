-- Prove2me | Theorems.Thm_BooleanIsoperimetry_PairShadowCost_le_neighborhood_embeddedPair_card
-- name    : BooleanIsoperimetry.PairShadowCost_le_neighborhood_embeddedPair_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:34:40.692803+00:00
-- url     : https://prove2.me/theorems/26fe10e7-0a69-4a82-b283-f7e9dfd7e2f5
-- title:
--   Boolean Isoperimetry: Pair Shadow Cost le neighborhood embedded Pair card
-- statement:
--   The paired slice functional is a lower bound for the literal neighborhood
--   size of the embedded family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L162-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L162-L172

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

theorem BooleanIsoperimetry.PairShadowCost_le_neighborhood_embeddedPair_card {N : ℕ} (A B : Finset (Cube N)) :
    PairShadowCost N A B ≤ (neighborhood 1 (embeddedPair N A B)).card := by sorry
