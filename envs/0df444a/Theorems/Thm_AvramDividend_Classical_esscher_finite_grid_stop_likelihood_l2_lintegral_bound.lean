-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:09:10.577569+00:00
-- url     : https://prove2.me/theorems/ba8d7ec6-1759-4349-af48-8b8b8d1816f9
-- title:
--   Uniform L2 bound for compensated Esscher densities sampled at finite-grid stopping times
-- statement:
--   For any adapted finite-grid τ≤H whose values precede terminal T, the P-lower integral of the squared compensated Esscher likelihood Mτ(θ)^2 is at most exp(H·|ψ(2θ)−2ψ(θ)|). The right side depends only on θ and H, not on the stopping grid or its resolution, and follows from the pointwise double-parameter domination plus the already-Proved fact that Mτ(2θ) is a probability density. This is a quantitative uniform-integrability bridge for bounded stopping limits.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012) Esscher exponential martingale; accepted finite-grid stopped-density probability 3c48c058-db76-437a-8d38-23370bbaa172 and prospective pointwise domination theorem; pinned Mathlib lintegral_mono, lintegral_const_mul and withDensity_apply.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_square_domination
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (hbound : ∀ ω, τ ω ≤ H) :
    (∫⁻ ω, ENNReal.ofReal
      (Real.exp ((2 * θ) * X.X (τ ω) ω -
        2 * (τ ω : ℝ) * X.ψ θ)) ∂P) ≤
      ENNReal.ofReal
        (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|)) := by sorry
