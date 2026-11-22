-- Prove2me | Theorems.Thm_BooleanIsoperimetry_compress_to_simplicial_pair
-- name    : BooleanIsoperimetry.compress_to_simplicial_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:40.469545+00:00
-- url     : https://prove2.me/theorems/3083a63e-93e0-4397-a66b-b97975000ac9
-- title:
--   Boolean Isoperimetry: compress to simplicial pair
-- statement:
--   **Phase 1 — within-slice compression to simplicial slices** (the paper's
--   "compress each family to a Hamming sphere of its own size").
--
--   For arbitrary slices `(A, B)`, replacing each by the simplicial initial segment of
--   its own cardinality does not increase the two-slice boundary cost.  Individual
--   cardinalities are preserved (`card (simplicialInitSeg N A.card) = A.card`), so this
--   is a within-slice move and the second arguments of the two `max`'s are unchanged;
--   the inequality then follows term-by-term from single-family vertex isoperimetry
--   `simplicialInitSeg_neighborhood_card_min` applied to each slice.
--
--   This is now **sorry-free**: it is a direct consequence of the single-family
--   compression result `simplicialInitSeg_neighborhood_card_min`, which in turn rests
--   on the Kruskal–Katona jump `exists_fullyCompressed_le` (via `upperLayerShadow_min`
--   = mathlib `Finset.kruskal_katona`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2222-L2233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2222-L2233

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

theorem BooleanIsoperimetry.compress_to_simplicial_pair {N : ℕ} (A B : Finset (Cube N)) :
    PairShadowCost N (simplicialInitSeg N A.card) (simplicialInitSeg N B.card)
      ≤ PairShadowCost N A B := by sorry
