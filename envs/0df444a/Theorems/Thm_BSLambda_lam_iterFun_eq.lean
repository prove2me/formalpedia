-- Prove2me | Theorems.Thm_BSLambda_lam_iterFun_eq
-- name    : BSLambda.lam_iterFun_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:37.291527+00:00
-- url     : https://prove2.me/theorems/f86a5984-6c6a-43b6-b6a1-71fa04676cb6
-- title:
--   BSLambda: lam iter Fun eq
-- statement:
--   `lambda(F_m) = lambda(f)^m` for the `m`-fold self-composition (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L529-L533
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L529-L533

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

theorem BSLambda.lam_iterFun_eq (f : Input V → Bool) : ∀ m, lam (iterFun f m) = lam f ^ m
  := by sorry
