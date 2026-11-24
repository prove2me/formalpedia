-- Prove2me | Theorems.Thm_BSLambda_Numerics_log_17_div_2_gt
-- name    : BSLambda.Numerics.log_17_div_2_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:22.237257+00:00
-- url     : https://prove2.me/theorems/e41621a4-f9b2-4ce7-af2a-594aa46c0e24
-- title:
--   Numerics: log 17 div 2 gt
-- statement:
--   Certified rational lower bound `2.138 < log (17/2)`, the second of the two logarithm
--   estimates required by the local-lemma verification in Section 10.2 of `bs_lambda.txt`.  The
--   true value is `2.1400661635…`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L90-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L90-L93

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.log_17_div_2_gt : (2.138 : ℝ) < Real.log (17 / 2) := by sorry
