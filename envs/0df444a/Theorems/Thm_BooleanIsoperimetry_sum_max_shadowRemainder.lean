-- Prove2me | Theorems.Thm_BooleanIsoperimetry_sum_max_shadowRemainder
-- name    : BooleanIsoperimetry.sum_max_shadowRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:27.860388+00:00
-- url     : https://prove2.me/theorems/d1985186-c55b-4a35-9efa-62e47147d106
-- title:
--   Boolean Isoperimetry: sum max shadow Remainder
-- statement:
--   **Per-layer max collapses to the global boundary value.**  Summing the
--   per-layer `max` of the shadow-cost window of `a` against the remainder window of
--   `b` over all Hamming layers recovers `max (H N a) b`, provided `b ≤ 2^N`.
--
--   The key structural fact is that *both* per-layer windows are layer counts of
--   nested simplicial initial segments: the shadow window of `a` is the layer count
--   of `simplicialInitSeg N (H N a)` (`layerCount_neighborhood_initSeg`), and the
--   remainder window of `b` is the layer count of `simplicialInitSeg N b`.  Initial
--   segments are nested, so on each layer the two counts are comparable and their
--   `max` is the layer count of `simplicialInitSeg N (max (H N a) b)`
--   (`max_layerWindow_eq_union_card`).  Summing over layers gives the cardinality
--   `min (max (H N a) b) (2^N) = max (H N a) b`, the last equality using `b ≤ 2^N`
--   and `H N a ≤ 2^N`.  This is exactly the statement that the global `max` commutes
--   with the per-layer decomposition for nested initial-segment windows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L201-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L201-L212

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset

theorem BooleanIsoperimetry.sum_max_shadowRemainder (N a b : ℕ) (hb : b ≤ 2 ^ N) :
    ∑ r ∈ Finset.range (N + 2),
        max (layerWindowShadowCost N r a) (layerWindowRemainder N r b)
      = max (H N a) b := by sorry
