-- Prove2me | Theorems.Thm_BSLambda_Numerics_le_mul_pow_mul_pow_of_lt_log
-- name    : BSLambda.Numerics.le_mul_pow_mul_pow_of_lt_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:11.902726+00:00
-- url     : https://prove2.me/theorems/e3e5a4e2-189b-4120-94a7-c0d7a07558a9
-- title:
--   Numerics: le mul pow mul pow of lt log
-- statement:
--   The analytic core of an asymmetric local-lemma condition: if `log c` exceeds the weighted
--   sum of the logarithmic losses `-log yᵢ`, then `p ≤ c p y₁^m y₂^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L56-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Logs.lean#L56-L63

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics

theorem BSLambda.Numerics.le_mul_pow_mul_pow_of_lt_log {p c y₁ y₂ : ℝ} {m n : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (h : (m : ℝ) * -Real.log y₁ + (n : ℝ) * -Real.log y₂ < Real.log c) :
    p ≤ c * p * y₁ ^ m * y₂ ^ n := by sorry
