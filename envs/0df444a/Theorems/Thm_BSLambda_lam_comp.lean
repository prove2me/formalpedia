-- Prove2me | Theorems.Thm_BSLambda_lam_comp
-- name    : BSLambda.lam_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:23.769213+00:00
-- url     : https://prove2.me/theorems/a5f8d031-85c4-4044-b8b0-92d947f83730
-- title:
--   BSLambda: lam comp
-- statement:
--   **The composition theorem** (Section 14 of `bs_lambda.txt`, imported there from ABKRT):
--   `lambda` is multiplicative under block composition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L512-L514
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L512-L514

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

theorem BSLambda.lam_comp (f : Input W → Bool) (g : Input V → Bool) :
    lam (comp f g) = lam f * lam g := by sorry
