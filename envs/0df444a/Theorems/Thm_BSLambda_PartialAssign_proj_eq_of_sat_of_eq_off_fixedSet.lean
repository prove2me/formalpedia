-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_proj_eq_of_sat_of_eq_off_fixedSet
-- name    : BSLambda.PartialAssign.proj_eq_of_sat_of_eq_off_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:27.835053+00:00
-- url     : https://prove2.me/theorems/356c4adf-4536-4afd-abf7-7cfe2c23f3e0
-- title:
--   Partial Assign: proj eq of sat of eq off fixed Set
-- statement:
--   A point that agrees with a point of `C(P)` off the coordinates fixed by `P` projects
--   onto it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L160-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L160-L165

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

theorem BSLambda.PartialAssign.proj_eq_of_sat_of_eq_off_fixedSet {P : PartialAssign V} {x y : Input V} (hx : P.Sat x)
    (h : ∀ v ∉ P.fixedSet, y v = x v) : P.proj y = x := by sorry
