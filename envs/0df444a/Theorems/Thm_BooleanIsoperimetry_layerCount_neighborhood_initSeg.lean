-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerCount_neighborhood_initSeg
-- name    : BooleanIsoperimetry.layerCount_neighborhood_initSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:27.886715+00:00
-- url     : https://prove2.me/theorems/5de7daff-cb07-406b-ad2f-603c8c11a67f
-- title:
--   Boolean Isoperimetry: layer Count neighborhood init Seg
-- statement:
--   The per-layer window counts of the neighborhood are the layer counts of the
--   *neighborhood-as-initial-segment* `simplicialInitSeg N (H N a)`.  This makes the
--   windows manifestly the Macaulay/binomial windows that the Kruskal–Katona core
--   `upperShadowVal_numeric_min` minimizes layer by layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L97-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L97-L100

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

theorem BooleanIsoperimetry.layerCount_neighborhood_initSeg (N r a : ℕ) :
    layerCount N r (neighborhood 1 (simplicialInitSeg N a)) =
      layerCount N r (simplicialInitSeg N (H N a)) := by sorry
