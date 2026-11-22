-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_one_filter_layer_eq_self_shadow_upShadow
-- name    : BooleanIsoperimetry.neighborhood_one_filter_layer_eq_self_shadow_upShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:09.086946+00:00
-- url     : https://prove2.me/theorems/1c9d2fce-c8fd-408b-a750-9dfc679a594b
-- title:
--   Boolean Isoperimetry: neighborhood one filter layer eq self shadow up Shadow
-- statement:
--   The Boolean Isoperimetry construction uses the neighborhood one filter layer eq self shadow up Shadow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1046-L1067
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1046-L1067

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

theorem BooleanIsoperimetry.neighborhood_one_filter_layer_eq_self_shadow_upShadow {N : ℕ}
    (A : Finset (Cube N)) (k : ℕ) :
    (neighborhood 1 A).filter (fun x => x.card = k) =
      (A.filter (fun x => x.card = k)) ∪
        ((Finset.shadow (A.filter (fun x => x.card = k + 1))).filter
          (fun x => x.card = k)) ∪
        ((Finset.upShadow (A.filter (fun x => x.card = k - 1))).filter
          (fun x => x.card = k)) := by sorry
