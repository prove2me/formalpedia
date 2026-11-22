-- Prove2me | Theorems.Thm_BooleanIsoperimetry_PairShadowCost_initSeg_eq_layerWindowCost
-- name    : BooleanIsoperimetry.PairShadowCost_initSeg_eq_layerWindowCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:12.888115+00:00
-- url     : https://prove2.me/theorems/b30bde6a-6f38-4f6b-9d68-54fb9bce8775
-- title:
--   Boolean Isoperimetry: Pair Shadow Cost init Seg eq layer Window Cost
-- statement:
--   **Phase-2 layer-window bridge (now sorry-free).**  On simplicial initial
--   segments the geometric two-slice cost `PairShadowCost` is exactly the explicit
--   layer-window cost `initSegPairLayerWindowCost` from `LayerWindows.lean`.
--
--   This is pure proof engineering, *not* Kruskal–Katona: on initial segments
--   `PairShadowCost` collapses to `max (H N a) b + max (H N b) a`
--   (`PairShadowCost_initSeg_eq_max_H`), and each boundary term `H N ·` is by
--   `neighborhoodLayerCost_eq_H` the finite sum over Hamming layers of the
--   neighborhood's per-layer window counts.  Filling the bridge removes the previous
--   "definition still missing" hole: `initSegPairLayerWindowCost` is now a real
--   layer-window sum, and the only remaining Phase-2 obligation is the genuine
--   cross-slice Kruskal–Katona minimization `cascade_layerWindowCost_min` below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2262-L2268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2262-L2268

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

theorem BooleanIsoperimetry.PairShadowCost_initSeg_eq_layerWindowCost
    {N a b : ℕ} (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    PairShadowCost N (simplicialInitSeg N a) (simplicialInitSeg N b) =
      initSegPairLayerWindowCost N a b := by sorry
