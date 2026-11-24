-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
-- name    : BSLambda.PartialAssign.indUnion_eq_false_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:18.699521+00:00
-- url     : https://prove2.me/theorems/67afce17-5127-46ef-81f3-fd30093f0641
-- title:
--   Partial Assign: ind Union eq false iff
-- statement:
--   The Partial Assign construction uses the ind Union eq false iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L254-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L254-L255

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
variable {ι : Type*} [Fintype ι]
variable {P : ι → PartialAssign V} {x : Input V}

theorem BSLambda.PartialAssign.indUnion_eq_false_iff : indUnion P x = false ↔ ∀ i, ¬ (P i).Sat x := by sorry
