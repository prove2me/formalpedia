-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_sat_unique_of_conflict
-- name    : BSLambda.PartialAssign.sat_unique_of_conflict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:47.678838+00:00
-- url     : https://prove2.me/theorems/ee1bff81-702d-4d9b-8f00-8d76da11a56f
-- title:
--   Partial Assign: sat unique of conflict
-- statement:
--   A point of the cube lies in at most one member of a pairwise conflicting family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L95-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L95-L100

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}

theorem BSLambda.PartialAssign.sat_unique_of_conflict {ι : Type*} {P : ι → PartialAssign V}
    (h : Pairwise fun i j ↦ ∃ v, (P i).Conflict (P j) v) {i j : ι} {x : Input V}
    (hi : (P i).Sat x) (hj : (P j).Sat x) : i = j := by sorry
