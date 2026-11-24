-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_dist_eq_card_violSet
-- name    : BSLambda.PartialAssign.dist_eq_card_violSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:03.471292+00:00
-- url     : https://prove2.me/theorems/1e42e565-1f2d-420f-ba6c-099302f0c9e0
-- title:
--   Partial Assign: dist eq card viol Set
-- statement:
--   The defining equation for `dist`, so that call sites need not unfold the `def`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L197-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L197-L198

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

theorem BSLambda.PartialAssign.dist_eq_card_violSet (P : PartialAssign V) (x : Input V) :
    P.dist x = (P.violSet x).card := by sorry
