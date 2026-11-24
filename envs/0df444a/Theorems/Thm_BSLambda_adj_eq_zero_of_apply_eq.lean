-- Prove2me | Theorems.Thm_BSLambda_adj_eq_zero_of_apply_eq
-- name    : BSLambda.adj_eq_zero_of_apply_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:58:33.403992+00:00
-- url     : https://prove2.me/theorems/11867c77-99fc-48d7-bbf4-1df0ca4eb24c
-- title:
--   BSLambda: adj eq zero of apply eq
-- statement:
--   Two inputs on the same side of `f` are never adjacent in the sensitivity graph.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L52-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Spectral.lean#L52-L54

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]

theorem BSLambda.adj_eq_zero_of_apply_eq (f : Input V → Bool) {x y : Input V} (h : f x = f y) :
    adj f x y = 0 := by sorry
