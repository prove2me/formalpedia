-- Prove2me | Theorems.Thm_BooleanIsoperimetry_PairLayerWindowCost_eq_zero_of_N_lt
-- name    : BooleanIsoperimetry.PairLayerWindowCost_eq_zero_of_N_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:42.294289+00:00
-- url     : https://prove2.me/theorems/2e91ecb1-e664-4fdc-807f-fb6cad3765e8
-- title:
--   Boolean Isoperimetry: Pair Layer Window Cost eq zero of N lt
-- statement:
--   The pair layer-window cost is zero above the top Hamming layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L140-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L140-L147

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

theorem BooleanIsoperimetry.PairLayerWindowCost_eq_zero_of_N_lt {N r a b : ℕ} (hNr : N < r) :
    PairLayerWindowCost N r a b = 0 := by sorry
