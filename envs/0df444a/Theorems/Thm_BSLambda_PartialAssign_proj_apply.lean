-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_proj_apply
-- name    : BSLambda.PartialAssign.proj_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:03.874092+00:00
-- url     : https://prove2.me/theorems/def1147e-73cc-401b-aea7-ffc0768ae246
-- title:
--   Partial Assign: proj apply
-- statement:
--   The projection keeps the value `P` fixes, falling back on the value of `x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L61-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L61-L62

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.proj_apply (P : PartialAssign V) (x : Input V) (v : V) :
    P.proj x v = (P v).getD (x v) := by sorry

attribute [defeq] BSLambda.PartialAssign.proj_apply
