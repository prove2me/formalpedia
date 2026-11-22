-- Prove2me | Theorems.Thm_BooleanIsoperimetry_disjoint_embed
-- name    : BooleanIsoperimetry.disjoint_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:33.719959+00:00
-- url     : https://prove2.me/theorems/c9ef7f98-bd7d-496a-beae-e9051215b276
-- title:
--   Boolean Isoperimetry: disjoint embed
-- statement:
--   The Boolean Isoperimetry construction uses the disjoint embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L208-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Shadow.lean#L208-L217

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

theorem BooleanIsoperimetry.disjoint_embed {N a b : ℕ} :
    Disjoint ((simplicialInitSeg N a).image embed0) ((simplicialInitSeg N b).image embed1) := by sorry
