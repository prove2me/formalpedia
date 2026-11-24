-- Prove2me | Theorems.Thm_BSLambda_Construction_mem_block
-- name    : BSLambda.Construction.mem_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:44.361808+00:00
-- url     : https://prove2.me/theorems/1562f394-f91b-45ce-8d7b-2ab4358f40e4
-- title:
--   Construction: mem block
-- statement:
--   The Construction construction uses the mem block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L53-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L53-L55

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

theorem BSLambda.Construction.mem_block {i : ι} {v : Coord ι r} : v ∈ block i ↔ v.1 = i := by sorry
