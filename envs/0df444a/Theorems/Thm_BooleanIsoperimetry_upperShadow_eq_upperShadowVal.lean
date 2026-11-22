-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadow_eq_upperShadowVal
-- name    : BooleanIsoperimetry.upperShadow_eq_upperShadowVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:37.051795+00:00
-- url     : https://prove2.me/theorems/bc1eead9-4131-4ca6-b5b8-af0ea8036cf7
-- title:
--   Boolean Isoperimetry: upper Shadow eq upper Shadow Val
-- statement:
--   The `Shadow.lean` numeric scaffold `upperShadow` and the relocated upstream
--   `upperShadowVal` are definitionally equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean#L43-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean#L43-L44

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

theorem BooleanIsoperimetry.upperShadow_eq_upperShadowVal (N r t : ℕ) :
    upperShadow N r t = upperShadowVal N r t := by sorry
