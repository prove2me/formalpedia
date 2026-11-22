-- Prove2me | Theorems.Thm_BooleanIsoperimetry_PairLayerWindowCost_eq_maxInitSeg
-- name    : BooleanIsoperimetry.PairLayerWindowCost_eq_maxInitSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:45.710297+00:00
-- url     : https://prove2.me/theorems/854f2838-2573-4daa-9acd-800c1262cb9f
-- title:
--   Boolean Isoperimetry: Pair Layer Window Cost eq max Init Seg
-- statement:
--   **Per-layer Macaulay closed form of the pair-window cost (sorry-free bridge).**
--
--   The opaque double-`max` cost `PairLayerWindowCost N r a b` is, *layer by layer*,
--   the sum of the layer-`r` counts of two **nested simplicial initial segments**
--   `simplicialInitSeg N (max (H N a) b)` and `simplicialInitSeg N (max (H N b) a)`.
--
--   The identification uses only two sorry-free dictionary facts already in
--   `LayerWindows.lean`:
--
--   * `layerWindowShadowCost_eq_remainder_H`: the shadow window of `a` is the
--     remainder window of the neighborhood size `H N a` (the unit neighborhood of an
--     initial segment is again an initial segment); and
--   * `max_layerWindow_eq_union_card`: since simplicial initial segments are nested,
--     the per-layer `max` of two remainder windows is the remainder window of the
--     segment of the larger size.
--
--   This turns every cross-slice window into an honest **Macaulay layer window** of a
--   single initial segment, so the cascade leaf below is a genuine Kruskal–Katona
--   initial-segment comparison rather than a scalar `H` inequality (rule 3).  It
--   needs no capacity hypotheses.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2332-L2339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2332-L2339

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

theorem BooleanIsoperimetry.PairLayerWindowCost_eq_maxInitSeg (N r a b : ℕ) :
    PairLayerWindowCost N r a b
      = layerWindowRemainder N r (max (H N a) b)
        + layerWindowRemainder N r (max (H N b) a) := by sorry
