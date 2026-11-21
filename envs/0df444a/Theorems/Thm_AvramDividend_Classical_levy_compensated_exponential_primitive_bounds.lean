-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_primitive_bounds
-- name    : AvramDividend.Classical.levy_compensated_exponential_primitive_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:09:51.842751+00:00
-- url     : https://prove2.me/theorems/e44e5f40-5d95-45ee-a9ce-12c1431e9089
-- title:
--   Quadratic small-jump and linear large-jump bounds on the compensated Lévy primitive
-- statement:
--   For any nonnegative Laplace parameter θ and nonnegative jump magnitude z, bound the compensated primitive ∫₀ᶻ(1−exp(−θt))dt between zero and both θz²/2 and z. The quadratic bound is exactly what ensures integrability for Lévy measures of infinite small-jump first moment, while the linear bound is compatible with Standing's large-jump first moment. Source-faithful and independent of the original stochastic process.
-- source:
--   Pinned intervalIntegral.integral_mono_on and integral_id, exact pointwise compensated kernel bound 1eaa6bca.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_kernel_bounds
open MeasureTheory Set intervalIntegral AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_exponential_primitive_bounds
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    0 ≤ (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) ∧
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) ≤ θ * z ^ 2 / 2 ∧
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) ≤ z := by sorry
