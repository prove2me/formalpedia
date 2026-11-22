-- Prove2me | Theorems.Thm_BooleanIsoperimetry_card_embed1
-- name    : BooleanIsoperimetry.card_embed1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:40.957284+00:00
-- url     : https://prove2.me/theorems/296618d0-2756-4d82-be4d-7e3ad8cdf347
-- title:
--   Boolean Isoperimetry: card embed1
-- statement:
--   The Boolean Isoperimetry construction uses the card embed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L223-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L223-L225

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

theorem BooleanIsoperimetry.card_embed1 {N b : ℕ} (hb : b ≤ 2 ^ N) :
    ((simplicialInitSeg N b).image embed1).card = b := by sorry
