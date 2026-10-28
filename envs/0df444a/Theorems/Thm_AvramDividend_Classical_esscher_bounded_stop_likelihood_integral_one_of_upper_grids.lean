-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one_of_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one_of_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:29:31.336676+00:00
-- url     : https://prove2.me/theorems/8132e3df-252c-497e-98c4-da1f11ec2895
-- title:
--   Bounded-stop Esscher likelihood has unit expectation from uniformly bounded adapted upper grids
-- statement:
--   Under P a probability, any genuine bounded stopping time τ that is approximated pointwise from above by finite-valued adapted stopping times bounded by a common H before T has exact Esscher likelihood mass E_P[exp(θX_τ−τψθ)]=1, for θ≥0. Uniform integrability follows from the genuine finite-grid quadratic-moment bound; no optional-stopping martingale theorem is assumed as a shortcut.
-- source:
--   Accepted conditional Vitali stopped-likelihood mass-one theorem 63ae3e6c plus forthcoming upper-grid actual uniform-integrability theorem 53937e78, which itself uses the proved L2 seminorm moment bound 62e997c8 and quantitative UI criterion 6ecde2f8.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one_of_upper_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by sorry
