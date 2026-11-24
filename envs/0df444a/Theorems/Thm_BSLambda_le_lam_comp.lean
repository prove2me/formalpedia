-- Prove2me | Theorems.Thm_BSLambda_le_lam_comp
-- name    : BSLambda.le_lam_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:21.275947+00:00
-- url     : https://prove2.me/theorems/c987888c-8f21-4d3c-8a04-08ccd49a4cc7
-- title:
--   BSLambda: le lam comp
-- statement:
--   **Supermultiplicativity of `lambda`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L499-L508
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L499-L508

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

theorem BSLambda.le_lam_comp (f : Input W → Bool) (g : Input V → Bool) :
    lam f * lam g ≤ lam (comp f g) := by sorry
