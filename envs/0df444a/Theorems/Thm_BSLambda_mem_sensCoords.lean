-- Prove2me | Theorems.Thm_BSLambda_mem_sensCoords
-- name    : BSLambda.mem_sensCoords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:08.541749+00:00
-- url     : https://prove2.me/theorems/9de99b69-8990-4c67-8870-ea8c817feea4
-- title:
--   BSLambda: mem sens Coords
-- statement:
--   The BSLambda construction uses the mem sens Coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L61-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L61-L62

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BSLambda.mem_sensCoords {f : Input V → Bool} {x : Input V} {v : V} :
    v ∈ sensCoords f x ↔ SensitiveCoord f x v := by sorry
