-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerWindowRemainder_eq_zero_of_N_lt
-- name    : BooleanIsoperimetry.layerWindowRemainder_eq_zero_of_N_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:22.607709+00:00
-- url     : https://prove2.me/theorems/4eaa03f0-2bac-431f-b5d4-b881ef6d1843
-- title:
--   Boolean Isoperimetry: layer Window Remainder eq zero of N lt
-- statement:
--   The remainder window is zero above the top Hamming layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L128-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L128-L131

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

theorem BooleanIsoperimetry.layerWindowRemainder_eq_zero_of_N_lt {N r a : ℕ} (hNr : N < r) :
    layerWindowRemainder N r a = 0 := by sorry
