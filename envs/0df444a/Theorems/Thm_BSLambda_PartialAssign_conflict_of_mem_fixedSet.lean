-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_conflict_of_mem_fixedSet
-- name    : BSLambda.PartialAssign.conflict_of_mem_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:57.474442+00:00
-- url     : https://prove2.me/theorems/7e3d0ca3-ed2b-40d1-abb4-948f513e8135
-- title:
--   Partial Assign: conflict of mem fixed Set
-- statement:
--   Converse of `Conflict.ne`: a coordinate fixed by both `P` and `Q` at which two
--   satisfying points differ is a conflict coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L232-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L232-L239

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

theorem BSLambda.PartialAssign.conflict_of_mem_fixedSet {P Q : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (hy : Q.Sat y) {v : V} (hP : v ∈ P.fixedSet) (hQ : v ∈ Q.fixedSet) (hne : x v ≠ y v) :
    P.Conflict Q v := by sorry
