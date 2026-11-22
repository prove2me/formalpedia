-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperLayerShadow_eq_filter_layer
-- name    : BooleanIsoperimetry.upperLayerShadow_eq_filter_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:29.575082+00:00
-- url     : https://prove2.me/theorems/a9eb7c63-b082-4da1-be94-46da4d39666a
-- title:
--   Boolean Isoperimetry: upper Layer Shadow eq filter layer
-- statement:
--   **Slice-reduction dictionary lemma.**  The upper layer shadow at layer `r`
--   depends only on the card-`r` slice of the family, because a card-`(r+1)` set lies
--   in `upShadow B` iff it contains some card-`r` member of `B`.  This is a direct
--   specialization of `upShadow_filter_layer_eq` at `k = r + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1971-L1975
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1971-L1975

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

theorem BooleanIsoperimetry.upperLayerShadow_eq_filter_layer {N r : ℕ} (B : Finset (Cube N)) :
    upperLayerShadow N r B = upperLayerShadow N r (B.filter (fun z => z.card = r)) := by sorry
