-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_violSet_subset_fixedSet
-- name    : BSLambda.PartialAssign.violSet_subset_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:55.386109+00:00
-- url     : https://prove2.me/theorems/697df5b3-72d3-4513-a805-69f667fa1851
-- title:
--   Partial Assign: viol Set subset fixed Set
-- statement:
--   The Partial Assign construction uses the viol Set subset fixed Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L181-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L181-L182

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

theorem BSLambda.PartialAssign.violSet_subset_fixedSet (P : PartialAssign V) (x : Input V) :
    P.violSet x ⊆ P.fixedSet := by sorry
