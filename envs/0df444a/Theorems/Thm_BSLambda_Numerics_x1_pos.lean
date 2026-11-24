-- Prove2me | Theorems.Thm_BSLambda_Numerics_x1_pos
-- name    : BSLambda.Numerics.x1_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:26.753015+00:00
-- url     : https://prove2.me/theorems/d5e0abf0-1844-4663-a491-6e9d22f3a4c5
-- title:
--   Numerics: x1 pos
-- statement:
--   The local-lemma parameter `x₁` is positive (Section 10.2 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L93-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L93-L93

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.x1_pos : 0 < x1 := by sorry
