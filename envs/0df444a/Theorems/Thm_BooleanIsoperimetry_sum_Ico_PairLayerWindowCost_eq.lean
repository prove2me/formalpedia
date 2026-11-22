-- Prove2me | Theorems.Thm_BooleanIsoperimetry_sum_Ico_PairLayerWindowCost_eq
-- name    : BooleanIsoperimetry.sum_Ico_PairLayerWindowCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:11.730734+00:00
-- url     : https://prove2.me/theorems/572daee4-9df5-40c4-ada1-398619ff1922
-- title:
--   Boolean Isoperimetry: sum Ico Pair Layer Window Cost eq
-- statement:
--   **Suffix layer-window sum in closed form (sorry-free Macaulay bridge).**
--
--   The upper-tail (Hamming layers `≥ k`) sum of the per-layer pair-window cost is,
--   exactly, the sum of the two truncated Macaulay neighborhood values
--   `max (H N a) b - binomPrefix N k` and `max (H N b) a - binomPrefix N k`
--   (truncated `ℕ` subtraction).  This is the composition of the two proved
--   dictionary facts `PairLayerWindowCost_eq_maxInitSeg` (each layer cost is a sum of
--   two nested initial-segment layer counts) and `suffix_layerWindowRemainder_eq`
--   (the suffix sum of an initial segment's layer counts is `m - binomPrefix N k`).
--   It turns the opaque suffix window sum into an explicit truncated-neighborhood
--   comparison over the Macaulay layer threshold `binomPrefix N k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2352-L2361
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2352-L2361

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

theorem BooleanIsoperimetry.sum_Ico_PairLayerWindowCost_eq (N a b k : ℕ)
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    ∑ r ∈ Finset.Ico k (N + 2), PairLayerWindowCost N r a b
      = (max (H N a) b - binomPrefix N k) + (max (H N b) a - binomPrefix N k) := by sorry
