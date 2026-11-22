-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadow_eq_card_upperLayerShadow
-- name    : BooleanIsoperimetry.upperShadow_eq_card_upperLayerShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:42.232233+00:00
-- url     : https://prove2.me/theorems/bdb74f41-fce2-4758-abb7-a36119631a8b
-- title:
--   Boolean Isoperimetry: upper Shadow eq card upper Layer Shadow
-- statement:
--   `Shadow.upperShadow` form of the partial-layer identity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean#L47-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean#L47-L51

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SetFamilyShadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.upperShadow_eq_card_upperLayerShadow {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadow N r t = (upperLayerShadow N r (layerInitSeg N r t)).card := by sorry
