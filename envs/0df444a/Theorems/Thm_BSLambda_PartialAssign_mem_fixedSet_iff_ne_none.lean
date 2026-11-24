-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_ne_none
-- name    : BSLambda.PartialAssign.mem_fixedSet_iff_ne_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:00.147935+00:00
-- url     : https://prove2.me/theorems/dcdb05df-5bbb-4bc4-a163-5940f05f7fc4
-- title:
--   Partial Assign: mem fixed Set iff ne none
-- statement:
--   The Partial Assign construction uses the mem fixed Set iff ne none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L138-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L138-L139

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

theorem BSLambda.PartialAssign.mem_fixedSet_iff_ne_none {P : PartialAssign V} {v : V} : v ∈ P.fixedSet ↔ P v ≠ none := by sorry
