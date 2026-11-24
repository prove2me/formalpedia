-- Prove2me | Theorems.Thm_BSLambda_Construction_block_nonempty
-- name    : BSLambda.Construction.block_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:45.930598+00:00
-- url     : https://prove2.me/theorems/61f09995-8ecc-44b7-83f2-0a4f687c924b
-- title:
--   Construction: block nonempty
-- statement:
--   The Construction construction uses the block nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L60-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L60-L61

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

theorem BSLambda.Construction.block_nonempty [NeZero r] (i : ι) : (block i : Finset (Coord ι r)).Nonempty := by sorry
