-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upShadow_filter_layer_eq
-- name    : BooleanIsoperimetry.upShadow_filter_layer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:43.442068+00:00
-- url     : https://prove2.me/theorems/89c94f5a-2988-45eb-b9ae-4c7f12579a4d
-- title:
--   Boolean Isoperimetry: up Shadow filter layer eq
-- statement:
--   Upper-shadow membership in a fixed output layer only depends on the previous
--   input layer.  The `k = 0` case is empty on the upper-shadow side, and the
--   `Nat.pred` formulation keeps the window statement total.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1020-L1044
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1020-L1044

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

theorem BooleanIsoperimetry.upShadow_filter_layer_eq {N : ℕ} (A : Finset (Cube N)) (k : ℕ) :
    (Finset.upShadow A).filter (fun x => x.card = k) =
      (Finset.upShadow (A.filter (fun x => x.card = k - 1))).filter
        (fun x => x.card = k) := by sorry
