-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_exists_sat_and_sat_of_forall_not_conflict
-- name    : BSLambda.PartialAssign.exists_sat_and_sat_of_forall_not_conflict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:25.816444+00:00
-- url     : https://prove2.me/theorems/3f77a738-ef62-49f2-8863-39e6ff2e9482
-- title:
--   Partial Assign: exists sat and sat of forall not conflict
-- statement:
--   Two partial assignments that conflict nowhere have a common point: merge them, taking
--   the value of `P` where `P` fixes a coordinate and the value of `Q` elsewhere.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L104-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L104-L113

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.exists_sat_and_sat_of_forall_not_conflict {P Q : PartialAssign V}
    (h : ∀ v, ¬ P.Conflict Q v) : ∃ x : Input V, P.Sat x ∧ Q.Sat x := by sorry
