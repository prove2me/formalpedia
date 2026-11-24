-- Prove2me | Theorems.Thm_BSLambda_Numerics_x1_lt_one
-- name    : BSLambda.Numerics.x1_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:49.873969+00:00
-- url     : https://prove2.me/theorems/b35e4506-fc24-4a41-bb1d-24b4f3553b7d
-- title:
--   Numerics: x1 lt one
-- statement:
--   The local-lemma parameter `x₁` lies below `1` (Section 10.2 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L99-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L99-L99

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.x1_lt_one : x1 < 1 := by sorry
