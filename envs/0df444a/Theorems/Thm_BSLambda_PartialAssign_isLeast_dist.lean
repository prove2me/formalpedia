-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_isLeast_dist
-- name    : BSLambda.PartialAssign.isLeast_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:55:06.772427+00:00
-- url     : https://prove2.me/theorems/b3d19a26-81fe-42f8-935b-0c20342339f9
-- title:
--   Partial Assign: is Least dist
-- statement:
--   `dist(x, C(P))` really is the minimum Hamming distance to the subcube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L281-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L281-L285

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

theorem BSLambda.PartialAssign.isLeast_dist (P : PartialAssign V) (x : Input V) :
    IsLeast (hammingDist x '' P.cube) (P.dist x) := by sorry
