-- Prove2me | Theorems.Thm_BSLambda_lam_iterFun_zero
-- name    : BSLambda.lam_iterFun_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:23.033091+00:00
-- url     : https://prove2.me/theorems/a0706d40-1da4-480a-83f5-594482a7bebf
-- title:
--   BSLambda: lam iter Fun zero
-- statement:
--   The one-bit identity function has `lambda = 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L519-L526
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L519-L526

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

theorem BSLambda.lam_iterFun_zero (f : Input V → Bool) : lam (iterFun f 0) = 1 := by sorry
