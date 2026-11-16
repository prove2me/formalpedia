-- Prove2me | solution 1 for thm_7_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:45.668125+00:00
-- url     : https://prove2.me/submissions/78df06fe-0d19-4c71-9100-01faa807e279

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory


/--
## Theorem 7.1: triangle inequality
for real- or complex-valued integrable
functions, the norm/absolute value of the integral
is bounded by the integral of the pointwise norm.

We use an existing API in Mathlib to finish the proof
-/
theorem solution {Ω 𝕜 : Type*}
  [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
  (X : Ω → 𝕜) (_hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  exact norm_integral_le_integral_norm X

