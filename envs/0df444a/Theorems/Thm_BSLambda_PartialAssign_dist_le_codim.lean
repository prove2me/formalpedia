-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_dist_le_codim
-- name    : BSLambda.PartialAssign.dist_le_codim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:55:03.478118+00:00
-- url     : https://prove2.me/theorems/8aecaf21-da8f-4952-8c16-a38b6bab171c
-- title:
--   Partial Assign: dist le codim
-- statement:
--   The Partial Assign construction uses the dist le codim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L200-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L200-L201

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]

theorem BSLambda.PartialAssign.dist_le_codim (P : PartialAssign V) (x : Input V) : P.dist x ≤ P.codim := by sorry
