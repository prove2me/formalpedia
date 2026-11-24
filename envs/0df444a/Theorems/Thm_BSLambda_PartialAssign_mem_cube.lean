-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_mem_cube
-- name    : BSLambda.PartialAssign.mem_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:17.490644+00:00
-- url     : https://prove2.me/theorems/f412bd10-5faf-46ed-98d0-28f5f313bad5
-- title:
--   Partial Assign: mem cube
-- statement:
--   The Partial Assign construction uses the mem cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L274-L275
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L274-L275

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

theorem BSLambda.PartialAssign.mem_cube {P : PartialAssign V} {x : Input V} : x ∈ P.cube ↔ P.Sat x := by sorry
