-- Prove2me | Theorems.Thm_BSLambda_Numerics_lll_cond_one
-- name    : BSLambda.Numerics.lll_cond_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:34.89868+00:00
-- url     : https://prove2.me/theorems/8646e390-5628-47ac-bb83-f23d390387ec
-- title:
--   Numerics: lll cond one
-- statement:
--   The type-1 asymmetric local-lemma condition
--   `p₁ ≤ x₁ (1-x₁)^{D₁₁} (1-x₂)^{D₁₂}` (Section 10.2 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L129-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L129-L133

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.lll_cond_one : p1 ≤ x1 * (1 - x1) ^ D11 * (1 - x2) ^ D12 := by sorry
