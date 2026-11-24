-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_eq_flipSet_proj_violSet
-- name    : BSLambda.PartialAssign.eq_flipSet_proj_violSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:36.797798+00:00
-- url     : https://prove2.me/theorems/d54876d4-cafd-42fe-a797-2658624f7d0b
-- title:
--   Partial Assign: eq flip Set proj viol Set
-- statement:
--   Every point is recovered from its projection onto `C(P)` by flipping exactly the
--   literals of `P` that it violates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L303-L312
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L303-L312

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

theorem BSLambda.PartialAssign.eq_flipSet_proj_violSet (P : PartialAssign V) (x : Input V) :
    x = flipSet (P.proj x) (P.violSet x) := by sorry
