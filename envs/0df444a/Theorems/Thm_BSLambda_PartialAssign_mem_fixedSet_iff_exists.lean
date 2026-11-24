-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists
-- name    : BSLambda.PartialAssign.mem_fixedSet_iff_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:46.783509+00:00
-- url     : https://prove2.me/theorems/8671624e-bd22-4cfa-8c4e-f691140af00e
-- title:
--   Partial Assign: mem fixed Set iff exists
-- statement:
--   A fixed coordinate carries an actual value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L142-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L142-L144

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

theorem BSLambda.PartialAssign.mem_fixedSet_iff_exists {P : PartialAssign V} {v : V} :
    v ∈ P.fixedSet ↔ ∃ b, P v = some b := by sorry
