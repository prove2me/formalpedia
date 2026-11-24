-- Prove2me | Theorems.Thm_BSLambda_Numerics_loss_two_lt
-- name    : BSLambda.Numerics.loss_two_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:34.549615+00:00
-- url     : https://prove2.me/theorems/61a07c5b-d31e-4e9c-b496-37e4cd8cec07
-- title:
--   Numerics: loss two lt
-- statement:
--   The type-2 loss sum is below `2.138` (Section 10.2 of `bs_lambda.txt`).  This is a
--   statement about explicit rationals. The true value is `2.1372344982481…`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L113-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L113-L114

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.loss_two_lt : (D21 : ℝ) * (x1 / (1 - x1)) + (D22 : ℝ) * (x2 / (1 - x2)) < 2.138 := by sorry
