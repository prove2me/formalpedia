-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerWindowShadowCost_eq_zero_of_N_lt
-- name    : BooleanIsoperimetry.layerWindowShadowCost_eq_zero_of_N_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:23.325023+00:00
-- url     : https://prove2.me/theorems/06c30163-5958-4989-b643-7961ec5b0d74
-- title:
--   Boolean Isoperimetry: layer Window Shadow Cost eq zero of N lt
-- statement:
--   The shadow-cost window is zero above the top Hamming layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L134-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L134-L137

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

theorem BooleanIsoperimetry.layerWindowShadowCost_eq_zero_of_N_lt {N r a : ℕ} (hNr : N < r) :
    layerWindowShadowCost N r a = 0 := by sorry
