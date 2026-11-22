-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice1_union_embed
-- name    : BooleanIsoperimetry.slice1_union_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:29.564805+00:00
-- url     : https://prove2.me/theorems/6e049886-ad8a-45fb-a14d-37541c2dec86
-- title:
--   Boolean Isoperimetry: slice1 union embed
-- statement:
--   The Boolean Isoperimetry construction uses the slice1 union embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L193-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L193-L206

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

theorem BooleanIsoperimetry.slice1_union_embed {N a b : ℕ} :
    slice1 ((simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1) =
      simplicialInitSeg N b := by sorry
