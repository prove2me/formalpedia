-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_proj_mem_cube
-- name    : BSLambda.PartialAssign.proj_mem_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:55:06.761609+00:00
-- url     : https://prove2.me/theorems/54b2c85e-9284-48cc-aee7-791368f1d758
-- title:
--   Partial Assign: proj mem cube
-- statement:
--   The Partial Assign construction uses the proj mem cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L277-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L277-L278

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.PartialAssign.proj_mem_cube (P : PartialAssign V) (x : Input V) : P.proj x ∈ P.cube := by sorry
