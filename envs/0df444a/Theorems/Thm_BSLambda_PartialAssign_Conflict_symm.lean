-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
-- name    : BSLambda.PartialAssign.Conflict.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:20.723244+00:00
-- url     : https://prove2.me/theorems/ef218930-0b49-47ab-be8f-090f49d47d05
-- title:
--   Conflict: symm
-- statement:
--   The Conflict construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L82-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L82-L85

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.Conflict.symm {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v) : Q.Conflict P v := by sorry
