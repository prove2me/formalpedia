-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_of_sat
-- name    : BSLambda.PartialAssign.indUnion_eq_true_of_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:02.479955+00:00
-- url     : https://prove2.me/theorems/2811f2b4-3b3d-44ea-852e-94d25703ebcf
-- title:
--   Partial Assign: ind Union eq true of sat
-- statement:
--   Every point of a member subcube is positive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L258-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L258-L259

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
variable {ι : Type*} [Fintype ι]
variable {P : ι → PartialAssign V} {x : Input V}

theorem BSLambda.PartialAssign.indUnion_eq_true_of_sat {i : ι} (h : (P i).Sat x) : indUnion P x = true := by sorry
