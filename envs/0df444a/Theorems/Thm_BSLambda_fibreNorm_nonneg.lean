-- Prove2me | Theorems.Thm_BSLambda_fibreNorm_nonneg
-- name    : BSLambda.fibreNorm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:38.25125+00:00
-- url     : https://prove2.me/theorems/9f8baf30-262d-4004-a57b-860b92cd2e8b
-- title:
--   BSLambda: fibre Norm nonneg
-- statement:
--   Fibre norms are nonnegative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L255-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L255-L257

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

theorem BSLambda.fibreNorm_nonneg (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) :
    0 ≤ fibreNorm g ψ b := by sorry
