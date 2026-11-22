-- Prove2me | Theorems.Thm_BooleanIsoperimetry_suffix_layerWindowRemainder_eq
-- name    : BooleanIsoperimetry.suffix_layerWindowRemainder_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:42.424185+00:00
-- url     : https://prove2.me/theorems/ca526f66-405b-4dea-810e-8135ca835041
-- title:
--   Boolean Isoperimetry: suffix layer Window Remainder eq
-- statement:
--   The Boolean Isoperimetry construction uses the suffix layer Window Remainder eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L309-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L309-L343

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

theorem BooleanIsoperimetry.suffix_layerWindowRemainder_eq (N m k : ℕ) (hm : m ≤ 2 ^ N) :
    ∑ r ∈ Finset.Ico k (N + 2), layerWindowRemainder N r m
      = m - binomPrefix N k := by sorry
