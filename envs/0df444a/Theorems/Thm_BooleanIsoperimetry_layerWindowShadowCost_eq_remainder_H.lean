-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerWindowShadowCost_eq_remainder_H
-- name    : BooleanIsoperimetry.layerWindowShadowCost_eq_remainder_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:27.654663+00:00
-- url     : https://prove2.me/theorems/e602c3f2-350e-4c56-bc1d-6c16e6518b6e
-- title:
--   Boolean Isoperimetry: layer Window Shadow Cost eq remainder H
-- statement:
--   The shadow-cost window of `a` in layer `r` is the *remainder* window of the
--   neighborhood size `H N a` in the same layer: the unit neighborhood of an initial
--   segment is again an initial segment (`neighborhood_initSeg_eq`), so its per-layer
--   counts are literally the per-layer counts of `simplicialInitSeg N (H N a)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L227-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L227-L230

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

theorem BooleanIsoperimetry.layerWindowShadowCost_eq_remainder_H (N r a : ℕ) :
    layerWindowShadowCost N r a = layerWindowRemainder N r (H N a) := by sorry
