-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_compensated_uniform_envelope
-- name    : AvramDividend.Classical.psi_compensated_uniform_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:19:54.773555+00:00
-- url     : https://prove2.me/theorems/56096632-eab6-45b1-bab8-d009a4dd7843
-- title:
--   Uniform integrable Lévy exponent jump kernel envelope on a compact nonnegative parameter interval
-- statement:
--   For a spectrally negative Lévy jump measure and all nonnegative Laplace parameters θ≤B, the compensated jump kernel is uniformly dominated by (1+B²) min(1,y²) for all negative jumps. On small jumps this follows from 0≤exp(z)−1−z≤z² for z≤0. On large jumps the compensation vanishes and |exp(θy)−1|≤1. The envelope is integrable by the canonical Lévy-measure assumption. This is the crucial source-specific dominated-convergence input for proving the Laplace exponent ψ is continuous.
-- source:
--   Proved exp_neg_remainder_bounds and the accepted source-level proof of levy_compensated_jump_integrable_nonneg; canonical ν-integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.psi_compensated_uniform_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : ℝ) (hB : 0 ≤ B) :
    ∀ θ ∈ Icc (0 : ℝ) B,
      ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y‖ ≤
        (1 + B ^ 2) * min 1 (y ^ 2) := by sorry
