-- Prove2me | Theorems.Thm_BSLambda_sum_sq_fibreNorm
-- name    : BSLambda.sum_sq_fibreNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:44.634173+00:00
-- url     : https://prove2.me/theorems/f75e73f5-8ccb-4f97-b068-bebce7a8f9ee
-- title:
--   BSLambda: sum sq fibre Norm
-- statement:
--   The fibre norms of `ψ` recombine into its `ℓ²`-norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L265-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L265-L267

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

theorem BSLambda.sum_sq_fibreNorm (g : Input V → Bool) (ψ : Input (W × V) → ℝ) :
    ∑ b : Input W, fibreNorm g ψ b ^ 2 = ∑ x : Input (W × V), ψ x ^ 2 := by sorry
