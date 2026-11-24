-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_eq_flipSet_proj_of_dist_eq_one
-- name    : BSLambda.PartialAssign.eq_flipSet_proj_of_dist_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:00.433051+00:00
-- url     : https://prove2.me/theorems/33cb81a9-d3a7-4a7c-8a05-282c0331c861
-- title:
--   Partial Assign: eq flip Set proj of dist eq one
-- statement:
--   A point at distance one from `C(P)` is a single flip of its projection, at the unique
--   violated coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L316-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L316-L320

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

theorem BSLambda.PartialAssign.eq_flipSet_proj_of_dist_eq_one {P : PartialAssign V} {x : Input V} (hd : P.dist x = 1) :
    ∃ v, P.violSet x = {v} ∧ x = flipSet (P.proj x) {v} := by sorry
