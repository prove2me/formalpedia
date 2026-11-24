-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
-- name    : BSLambda.PartialAssign.mem_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:05.184427+00:00
-- url     : https://prove2.me/theorems/64903886-bfc7-458e-947b-1b4a57a7f207
-- title:
--   Partial Assign: mem fixed Set
-- statement:
--   The Partial Assign construction uses the mem fixed Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L135-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L135-L136

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

theorem BSLambda.PartialAssign.mem_fixedSet {P : PartialAssign V} {v : V} :
    v ∈ P.fixedSet ↔ (P v).isSome := by sorry
