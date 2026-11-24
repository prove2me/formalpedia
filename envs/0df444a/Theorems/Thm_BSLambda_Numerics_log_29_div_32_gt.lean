-- Prove2me | Theorems.Thm_BSLambda_Numerics_log_29_div_32_gt
-- name    : BSLambda.Numerics.log_29_div_32_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:15.183056+00:00
-- url     : https://prove2.me/theorems/a278fa80-1945-4822-9ccb-6689632f5c1a
-- title:
--   Numerics: log 29 div 32 gt
-- statement:
--   Cubic Taylor lower bound for `log (29/32) = log (1 - 3/32)`.  The exact bound the Taylor
--   estimate gives is `-(3225/32768) - 81/950272 = -0.09850442…`; the true value is
--   `-0.09806…`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L70-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L70-L73

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.log_29_div_32_gt : (-0.0986 : ℝ) < Real.log (29 / 32) := by sorry
