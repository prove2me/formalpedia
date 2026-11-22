-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerWindowRemainder_le_choose
-- name    : BooleanIsoperimetry.layerWindowRemainder_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:15.576808+00:00
-- url     : https://prove2.me/theorems/a8dd2c32-1cf7-4fcf-b3e4-3a1fac000dda
-- title:
--   Boolean Isoperimetry: layer Window Remainder le choose
-- statement:
--   The layer-`r` window of an initial segment never exceeds the number of
--   `r`-subsets `Nat.choose N r`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L241-L244
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L241-L244

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

theorem BooleanIsoperimetry.layerWindowRemainder_le_choose (N r a : ℕ) :
    layerWindowRemainder N r a ≤ Nat.choose N r := by sorry
