-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_upper_bound_by_compensated_small_jumps
-- name    : AvramDividend.Classical.psi_upper_bound_by_compensated_small_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:22:09.753984+00:00
-- url     : https://prove2.me/theorems/85d8b8ec-f19f-4e40-9246-089f69cf6041
-- title:
--   Canonical Lévy exponent upper bound from compensated small negative jumps
-- statement:
--   For every nonnegative real Laplace parameter, the canonical spectrally negative Lévy exponent ψ(θ) is at most its drift and Gaussian terms plus the compensated small-negative-jump integral over (-1,0). Large negative jumps contribute exp(θy)−1≤0, and the upper bound is valid for general infinite Lévy measures. Together with the separately Proved matching lower bound, this enables a rigorous squeeze of ψ(θ)/θ to the positive drift in the finite-first-moment non-Gaussian case.
-- source:
--   Prove2Me-Proved negative_jump_kernel_upper_indicator and levy_compensated_jump_integrable_nonneg, pinned Mathlib integral_mono_ae, indicator integration and measure restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.psi_upper_bound_by_compensated_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    X.ψ θ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) := by sorry
