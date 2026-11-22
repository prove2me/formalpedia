-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadowVal_eq_card_upperLayerShadow
-- name    : BooleanIsoperimetry.upperShadowVal_eq_card_upperLayerShadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:05.532586+00:00
-- url     : https://prove2.me/theorems/6aee88a8-65ab-4e17-ac43-5b63c5871bd3
-- title:
--   Boolean Isoperimetry: upper Shadow Val eq card upper Layer Shadow
-- statement:
--   The Boolean Isoperimetry construction uses the upper Shadow Val eq card upper Layer Shadow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L245-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L245-L328

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry

theorem BooleanIsoperimetry.upperShadowVal_eq_card_upperLayerShadow {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) :
    upperShadowVal N r t = (upperLayerShadow N r (layerInitSeg N r t)).card := by sorry
