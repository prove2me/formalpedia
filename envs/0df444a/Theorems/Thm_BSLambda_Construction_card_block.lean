-- Prove2me | Theorems.Thm_BSLambda_Construction_card_block
-- name    : BSLambda.Construction.card_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:52.233584+00:00
-- url     : https://prove2.me/theorems/b05b8bf3-e56b-47e0-bf42-301790dd1d07
-- title:
--   Construction: card block
-- statement:
--   The Construction construction uses the card block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L57-L58

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}

theorem BSLambda.Construction.card_block (i : ι) : (block i : Finset (Coord ι r)).card = r := by sorry
