-- Prove2me | Theorems.Thm_BSLambda_Numerics_add_mul_neg_log_one_sub_le
-- name    : BSLambda.Numerics.add_mul_neg_log_one_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:16.604023+00:00
-- url     : https://prove2.me/theorems/c22223b9-039c-4a69-9c2c-1e198296c4e3
-- title:
--   Numerics: add mul neg log one sub le
-- statement:
--   The logarithmic losses at `x₁` and `x₂`, weighted by two dependency counts, are bounded
--   by the corresponding sum of exact rationals (Section 10.2 of `bs_lambda.txt`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L118-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/LLLBounds.lean#L118-L123

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.add_mul_neg_log_one_sub_le (m n : ℕ) :
    (m : ℝ) * -Real.log (1 - x1) + (n : ℝ) * -Real.log (1 - x2) ≤
      (m : ℝ) * (x1 / (1 - x1)) + (n : ℝ) * (x2 / (1 - x2)) := by sorry
