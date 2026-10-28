-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_square_domination
-- name    : AvramDividend.Classical.esscher_bounded_stop_likelihood_square_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:53:07.615411+00:00
-- url     : https://prove2.me/theorems/e4540632-7a60-4805-baa4-5887480e2684
-- title:
--   Pointwise uniform second-moment domination for bounded stopped Esscher likelihoods
-- statement:
--   For any bounded nonnegative random time τ≤H, regardless of whether it is a stopping time, the exponential corresponding to the square of the compensated Esscher likelihood at parameter θ is bounded pathwise by exp(H·|ψ(2θ)−2ψ(θ)|) times the compensated Esscher likelihood at parameter 2θ evaluated at τ. This exact exponential identity and deterministic bound is the quantitative L²/uniform-integrability step for finite-grid approximations to genuine bounded stops; no optional-stopping, global tilted law, or Wiener–Hopf assumption is used.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012) Esscher martingale transform and finiteness of nonnegative Laplace exponents; elementary identity M_τ(θ)^2=M_τ(2θ)exp(τ(ψ(2θ)−2ψ(θ))) and pinned Mathlib Real.exp_add, Real.exp_le_exp, NNReal order casts.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_likelihood_square_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0) (H : ℝ≥0)
    (hbound : ∀ ω, τ ω ≤ H) (ω : Ω) :
    Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ) ≤
      Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) *
        Real.exp ((2 * θ) * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ (2 * θ)) := by sorry
