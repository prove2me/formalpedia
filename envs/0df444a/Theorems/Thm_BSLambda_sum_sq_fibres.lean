-- Prove2me | Theorems.Thm_BSLambda_sum_sq_fibres
-- name    : BSLambda.sum_sq_fibres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:30.111896+00:00
-- url     : https://prove2.me/theorems/1f844047-53d1-44cb-b483-a8095617307f
-- title:
--   BSLambda: sum sq fibres
-- statement:
--   The fibres of `topBits g` partition the inputs, so the squares of the fibrewise truncations
--   of `F` sum to `∑ x, F x ^ 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L242-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L242-L248

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

theorem BSLambda.sum_sq_fibres (g : Input V → Bool) (F : Input (W × V) → ℝ) :
    ∑ b : Input W, ∑ x : Input (W × V), (if topBits g x = b then F x else 0) ^ 2
      = ∑ x : Input (W × V), F x ^ 2 := by sorry
