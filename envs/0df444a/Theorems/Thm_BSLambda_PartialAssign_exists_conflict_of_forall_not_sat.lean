-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_exists_conflict_of_forall_not_sat
-- name    : BSLambda.PartialAssign.exists_conflict_of_forall_not_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:55:01.35923+00:00
-- url     : https://prove2.me/theorems/cdad70f0-1675-455b-be85-cea591a6632e
-- title:
--   Partial Assign: exists conflict of forall not sat
-- statement:
--   Converse of `Conflict.disjoint_cube`: disjoint subcubes come from a conflicting pair of
--   literals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L117-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L117-L121

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.exists_conflict_of_forall_not_sat {P Q : PartialAssign V}
    (h : ∀ x : Input V, P.Sat x → ¬ Q.Sat x) : ∃ v, P.Conflict Q v := by sorry
