-- Prove2me | Theorems.Thm_BSLambda_Numerics_log_17_div_16_gt
-- name    : BSLambda.Numerics.log_17_div_16_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:14.992372+00:00
-- url     : https://prove2.me/theorems/33d878e5-4de2-4d66-af1c-40a29b1ac354
-- title:
--   Numerics: log 17 div 16 gt
-- statement:
--   Lower bound `1/17 < log (17/16)`, from `log t < t - 1` at `t = 16/17`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L76-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L76-L78

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.log_17_div_16_gt : (1 / 17 : ℝ) < Real.log (17 / 16) := by sorry
