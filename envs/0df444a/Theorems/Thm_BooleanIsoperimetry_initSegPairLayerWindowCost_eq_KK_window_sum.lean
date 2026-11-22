-- Prove2me | Theorems.Thm_BooleanIsoperimetry_initSegPairLayerWindowCost_eq_KK_window_sum
-- name    : BooleanIsoperimetry.initSegPairLayerWindowCost_eq_KK_window_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:23.544264+00:00
-- url     : https://prove2.me/theorems/2fa1a742-7609-4231-a5d5-99414a2ed64b
-- title:
--   Boolean Isoperimetry: init Seg Pair Layer Window Cost eq KK window sum
-- statement:
--   **Layer-window decomposition of the pair cost.**  The
--   scalar two-slice cost `initSegPairLayerWindowCost N a b` is the sum over Hamming
--   layers of the per-layer pair window costs `PairLayerWindowCost N r a b`.  This is
--   the bookkeeping bridge exposing the Macaulay/Kruskal–Katona layer windows that
--   the cross-slice leaf `cascade_window_sum_min` (`Compression.lean`) operates on
--   it requires `a, b ≤ 2^N` (otherwise the literal cross terms `a`/`b` exceed the
--   saturated initial-segment cardinality `2^N` and the identity fails).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L265-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L265-L272

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

theorem BooleanIsoperimetry.initSegPairLayerWindowCost_eq_KK_window_sum (N a b : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    initSegPairLayerWindowCost N a b =
      ∑ r ∈ Finset.range (N + 2), PairLayerWindowCost N r a b := by sorry
