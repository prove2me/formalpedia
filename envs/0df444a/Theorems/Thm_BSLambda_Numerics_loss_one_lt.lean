-- Prove2me | Theorems.Thm_BSLambda_Numerics_loss_one_lt
-- name    : BSLambda.Numerics.loss_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:30.677122+00:00
-- url     : https://prove2.me/theorems/05ed6530-21d1-4549-90cc-cd465cb1b5c3
-- title:
--   Numerics: loss one lt
-- statement:
--   The type-1 loss sum is below `0.594` (Section 10.2 of `bs_lambda.txt`).  This is a
--   statement about explicit rationals. The true value is `0.5938861514605…`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L108-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L108-L109

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.loss_one_lt : (D11 : ℝ) * (x1 / (1 - x1)) + (D12 : ℝ) * (x2 / (1 - x2)) < 0.594 := by sorry
