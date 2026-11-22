-- Prove2me | Theorems.Thm_BooleanIsoperimetry_shadow_filter_layer_eq
-- name    : BooleanIsoperimetry.shadow_filter_layer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:04.864554+00:00
-- url     : https://prove2.me/theorems/6478ce8d-c731-4916-a451-94b90fb2f4b9
-- title:
--   Boolean Isoperimetry: shadow filter layer eq
-- statement:
--   Lower-shadow membership in a fixed output layer only depends on the next
--   input layer.  This is the local Hamming-window dictionary used by the
--   layer-by-layer closed-neighborhood argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L991-L1015
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L991-L1015

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

theorem BooleanIsoperimetry.shadow_filter_layer_eq {N : ℕ} (A : Finset (Cube N)) (k : ℕ) :
    (Finset.shadow A).filter (fun x => x.card = k) =
      (Finset.shadow (A.filter (fun x => x.card = k + 1))).filter
        (fun x => x.card = k) := by sorry
