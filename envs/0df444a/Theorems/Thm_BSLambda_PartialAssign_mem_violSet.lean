-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_mem_violSet
-- name    : BSLambda.PartialAssign.mem_violSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:01.714495+00:00
-- url     : https://prove2.me/theorems/1d9f6662-1003-4426-a18c-a6adb75c8da2
-- title:
--   Partial Assign: mem viol Set
-- statement:
--   The Partial Assign construction uses the mem viol Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L173-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L173-L174

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

theorem BSLambda.PartialAssign.mem_violSet {P : PartialAssign V} {x : Input V} {v : V} :
    v ∈ P.violSet x ↔ P v ≠ none ∧ P v ≠ some (x v) := by sorry
