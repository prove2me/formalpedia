-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_Conflict_disjoint_cube
-- name    : BSLambda.PartialAssign.Conflict.disjoint_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:32.078435+00:00
-- url     : https://prove2.me/theorems/26f0a204-858f-477a-9fc4-301a10d8ba06
-- title:
--   Conflict: disjoint cube
-- statement:
--   If `P` and `Q` conflict somewhere then their subcubes are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L288-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L288-L290

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.PartialAssign.Conflict.disjoint_cube {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v) :
    Disjoint P.cube Q.cube := by sorry
