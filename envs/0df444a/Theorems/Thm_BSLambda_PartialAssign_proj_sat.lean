-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_proj_sat
-- name    : BSLambda.PartialAssign.proj_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:04.07335+00:00
-- url     : https://prove2.me/theorems/bfad073e-da76-4e7b-819a-2d71bf07cb82
-- title:
--   Partial Assign: proj sat
-- statement:
--   The Partial Assign construction uses the proj sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L64-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L64-L66

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.proj_sat (P : PartialAssign V) (x : Input V) : P.Sat (P.proj x) := by sorry
