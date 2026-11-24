-- Prove2me | Theorems.Thm_BSLambda_Numerics_neg_log_one_sub_le
-- name    : BSLambda.Numerics.neg_log_one_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:13.901969+00:00
-- url     : https://prove2.me/theorems/f72b516d-843d-4ce2-b84f-fa5f379aafe2
-- title:
--   Numerics: neg log one sub le
-- statement:
--   For `y < 1` one has `-log (1-y) ≤ y / (1-y)`; a repackaging of
--   `Real.one_sub_inv_le_log_of_pos`, and the elementary estimate used in Section 10.2 of
--   `bs_lambda.txt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L49-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L49-L52

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.neg_log_one_sub_le {y : ℝ} (hy : y < 1) : -Real.log (1 - y) ≤ y / (1 - y) := by sorry
