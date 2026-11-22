-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice0_union_embed
-- name    : BooleanIsoperimetry.slice0_union_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:32.321801+00:00
-- url     : https://prove2.me/theorems/8c5e6d81-71cc-4814-851f-f89e56ec26c2
-- title:
--   Boolean Isoperimetry: slice0 union embed
-- statement:
--   The Boolean Isoperimetry construction uses the slice0 union embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L178-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L178-L191

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

theorem BooleanIsoperimetry.slice0_union_embed {N a b : ℕ} :
    slice0 ((simplicialInitSeg N a).image embed0 ∪ (simplicialInitSeg N b).image embed1) =
      simplicialInitSeg N a := by sorry
