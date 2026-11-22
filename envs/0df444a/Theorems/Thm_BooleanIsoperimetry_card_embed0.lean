-- Prove2me | Theorems.Thm_BooleanIsoperimetry_card_embed0
-- name    : BooleanIsoperimetry.card_embed0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:34.203944+00:00
-- url     : https://prove2.me/theorems/6f9acdf3-1f9e-429a-b807-800802e4548b
-- title:
--   Boolean Isoperimetry: card embed0
-- statement:
--   The Boolean Isoperimetry construction uses the card embed0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L219-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L219-L221

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.card_embed0 {N a : ℕ} (ha : a ≤ 2 ^ N) :
    ((simplicialInitSeg N a).image embed0).card = a := by sorry
