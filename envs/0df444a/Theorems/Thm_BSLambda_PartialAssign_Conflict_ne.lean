-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_Conflict_ne
-- name    : BSLambda.PartialAssign.Conflict.ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:47.634764+00:00
-- url     : https://prove2.me/theorems/a949bba3-401b-4077-81d0-4b724efbebea
-- title:
--   Conflict: ne
-- statement:
--   Points of two conflicting subcubes disagree at the conflict coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L88-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L88-L92

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.Conflict.ne {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v)
    {x y : Input V} (hx : P.Sat x) (hy : Q.Sat y) : x v ≠ y v := by sorry
