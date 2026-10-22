-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_absolute_integrable
-- name    : AvramDividend.Classical.gaussian_levy_jump_absolute_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:33:32.556535+00:00
-- url     : https://prove2.me/theorems/40e71174-a6b1-4cbe-91f4-0496b55b3275
-- title:
--   Finite absolute integral of canonical Lévy jump exponent
-- statement:
--   For nonnegative exponential argument θ and a positive jump-magnitude Lévy measure satisfying ∫min(1,z²)μ(dz)<∞, the original negative-jump exponent exp(−θz)−1+θ z 1_{z≤1} is absolutely integrable in the extended-nonnegative sense. Use the separate sharp scalar bound by (1+θ²)min(1,z²) and exact monotonicity and constant multiplication of lintegrals. This supports the complete real Lévy–Khintchine exponent under the canonical truncation.
-- source:
--   Requires proved gaussian_levy_jump_truncation_envelope; ENNReal.ofReal_mul, lintegral_mono_ae, lintegral_const_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_levy_jump_absolute_integrable
    (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal
      |Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)| ∂μ) < ⊤ := by sorry
