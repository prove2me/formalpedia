-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_embeddedPair_card
-- name    : BooleanIsoperimetry.neighborhood_embeddedPair_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:39.252504+00:00
-- url     : https://prove2.me/theorems/bf895ce4-8d77-41fb-8bf0-1ffd658beb9f
-- title:
--   Boolean Isoperimetry: neighborhood embedded Pair card
-- statement:
--   Exact neighborhood decomposition for an embedded two-slice family.  This is
--   the literal cardinality of the closed unit neighborhood in `Q_{N+1}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L98-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L98-L101

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

theorem BooleanIsoperimetry.neighborhood_embeddedPair_card {N : ℕ} (A B : Finset (Cube N)) :
    (neighborhood 1 (embeddedPair N A B)).card =
      (neighborhood 1 A ∪ B).card + (neighborhood 1 B ∪ A).card := by sorry
