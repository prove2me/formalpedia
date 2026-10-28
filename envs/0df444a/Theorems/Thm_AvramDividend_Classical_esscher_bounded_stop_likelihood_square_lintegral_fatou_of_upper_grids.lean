-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_square_lintegral_fatou_of_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_likelihood_square_lintegral_fatou_of_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:04:03.430996+00:00
-- url     : https://prove2.me/theorems/99d9047b-a7c0-4547-b8e6-d64f6baa27c3
-- title:
--   Fatou transfer of the uniform finite-grid Esscher second-moment bound to an upper-grid approximated bounded time
-- statement:
--   For an arbitrary bounded time approached pointwise from above by adapted finite-valued stopping grids with a common cap H, the stopped compensated Esscher likelihood at the limit has finite second moment bounded by the same uniform constant exp(H |ψ(2θ)-2ψθ|). This uses pathwise right continuity and Fatou; no L¹ optional sampling identity is presupposed.
-- source:
--   Kuznetsov–Kyprianou–Rivero Esscher exponent, accepted 1E-A finite-grid squared-likelihood bound ba8d7ec6, accepted 1E-A right limit fee892e8, accepted joint Levy measurability d55462c3, pinned Mathlib lintegral_liminf_le and Filter.Tendsto.liminf_eq.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_likelihood_square_lintegral_fatou_of_upper_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n → s ≤ T)
    (hstop : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    (∫⁻ ω, ENNReal.ofReal
      ((Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)) ^ 2) ∂P) ≤
      ENNReal.ofReal
        (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|)) := by sorry
