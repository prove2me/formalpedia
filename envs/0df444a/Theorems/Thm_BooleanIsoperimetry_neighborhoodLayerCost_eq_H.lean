-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhoodLayerCost_eq_H
-- name    : BooleanIsoperimetry.neighborhoodLayerCost_eq_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:28.160447+00:00
-- url     : https://prove2.me/theorems/35c52b11-60c6-4800-a2ae-5beeb3ad2c78
-- title:
--   Boolean Isoperimetry: neighborhood Layer Cost eq H
-- statement:
--   The layer-window sum reconstructs the boundary functional `H`: summing the
--   per-layer window counts of the neighborhood over all Hamming layers recovers its
--   cardinality `H N a`.  (Every vertex of the `N`-cube has cardinality `≤ N < N+2`,
--   so the layers `0, …, N+1` partition the neighborhood.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L80-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L80-L91

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

theorem BooleanIsoperimetry.neighborhoodLayerCost_eq_H (N a : ℕ) :
    neighborhoodLayerCost N a = H N a := by sorry
