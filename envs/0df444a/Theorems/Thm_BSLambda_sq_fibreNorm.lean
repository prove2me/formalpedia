-- Prove2me | Theorems.Thm_BSLambda_sq_fibreNorm
-- name    : BSLambda.sq_fibreNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:25.535282+00:00
-- url     : https://prove2.me/theorems/8bc1cfb4-65be-43de-9200-7b33e7ddf166
-- title:
--   BSLambda: sq fibre Norm
-- statement:
--   The defining property of the fibre norm, with the square root cleared.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L260-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L260-L262

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

theorem BSLambda.sq_fibreNorm (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) :
    fibreNorm g ψ b ^ 2 = ∑ x : Input (W × V), (if topBits g x = b then ψ x else 0) ^ 2 := by sorry
