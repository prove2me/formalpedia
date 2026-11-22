-- Prove2me | Theorems.Thm_BooleanIsoperimetry_max_layerWindow_eq_union_card
-- name    : BooleanIsoperimetry.max_layerWindow_eq_union_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:32.409839+00:00
-- url     : https://prove2.me/theorems/adad4aca-1aea-4bef-863d-6ab2fd443916
-- title:
--   Boolean Isoperimetry: max layer Window eq union card
-- statement:
--   The Boolean Isoperimetry construction uses the max layer Window eq union card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L149-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L149-L168

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

theorem BooleanIsoperimetry.max_layerWindow_eq_union_card (N r X Y : ℕ) :
    max (layerCount N r (simplicialInitSeg N X)) (layerCount N r (simplicialInitSeg N Y)) =
    layerCount N r (simplicialInitSeg N (max X Y)) := by sorry
