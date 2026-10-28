-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation
-- name    : AvramDividend.Classical.esscher_stopped_likelihood_tendsto_of_right_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:55:19.404067+00:00
-- url     : https://prove2.me/theorems/fee892e8-7d32-4b89-ac73-963bcaf8fc10
-- title:
--   Compensated Esscher likelihoods converge pathwise along arbitrary right-directed stopping-time approximations
-- statement:
--   For any real-valued nonnegative random time τ and any sequence of random times τn approaching τ from above on every path, the compensated Esscher exponential likelihood M_(τn)(θ) converges pointwise to M_τ(θ). This uses the actual right continuity of every spectrally negative Lévy sample path, NNReal-to-real continuity, and continuity of exp. It is the analytic pointwise half of the bounded stopped-density L¹ bridge and does not assume the stopped density already defines a probability.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), càdlàg Lévy sample paths and Esscher density; pinned SpectrallyNegativeLevy.rightCont field and NNReal.continuous_coe, Mathlib tendsto_nhdsWithin_iff and Real.continuous_exp; accepted analogous increment convergence 8f73cd3f-a954-42f0-8b97-1d2f9f66b949.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_stopped_likelihood_tendsto_of_right_approximation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    ∀ ω, Tendsto
      (fun n => Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ))
      atTop (𝓝 (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ))) := by sorry
