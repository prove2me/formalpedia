-- Prove2me | Theorems.Thm_BooleanIsoperimetry_sum_Ico_layerWindowRemainder_max_eq
-- name    : BooleanIsoperimetry.sum_Ico_layerWindowRemainder_max_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:40.042952+00:00
-- url     : https://prove2.me/theorems/90372366-90ef-4b1e-a08d-0799f1be9005
-- title:
--   Boolean Isoperimetry: sum Ico layer Window Remainder max eq
-- statement:
--   **Suffix layer-window sum as a Hamming upper-tail count of a neighborhood union.**
--
--   The upper-tail (Hamming layers `≥ k`) sum of the remainder windows of the value
--   `max (H N x) y` is exactly the number of vertices of cardinality `≥ k` in the
--   union of the unit neighborhood of the initial segment of size `x` with the
--   initial segment of size `y`.  This is a sorry-free dictionary identity: the unit
--   neighborhood of an initial segment is again an initial segment
--   (`neighborhood_initSeg_eq`), initial segments are nested so their union is the
--   initial segment of the larger size, and the suffix layer sum of an initial
--   segment counts exactly its vertices of cardinality `≥ k`
--   (`sum_Ico_layerCount_eq_filter_card_ge`).  It converts the opaque window sum into
--   the genuine set-family Hamming upper-tail count on which the dimension recursion
--   operates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2376-L2388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2376-L2388

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

theorem BooleanIsoperimetry.sum_Ico_layerWindowRemainder_max_eq (N x y k : ℕ) :
    ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r (max (H N x) y)
      = ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y).filter
          (fun z => k ≤ z.card)).card := by sorry
