-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_hammingDist_proj
-- name    : BSLambda.PartialAssign.hammingDist_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:29.719267+00:00
-- url     : https://prove2.me/theorems/0be75298-02f7-41a1-bc0c-61801a0e8313
-- title:
--   Partial Assign: hamming Dist proj
-- statement:
--   The distance to `C(P)` is realised by the projection.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L209-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L209-L215

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

theorem BSLambda.PartialAssign.hammingDist_proj (P : PartialAssign V) (x : Input V) :
    hammingDist x (P.proj x) = P.dist x := by sorry
