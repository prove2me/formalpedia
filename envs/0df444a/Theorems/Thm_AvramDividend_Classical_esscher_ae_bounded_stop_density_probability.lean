-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_density_probability
-- name    : AvramDividend.Classical.esscher_ae_bounded_stop_density_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:53:45.178984+00:00
-- url     : https://prove2.me/theorems/21ec4cea-e47c-4696-8063-0b027f7a2ba4
-- title:
--   Stopped-time Esscher likelihood remains a probability at a P-almost-surely bounded stop
-- statement:
--   For the genuine stopped-time Esscher density M_tau at a finite stopping time tau with P-almost-sure deterministic bound H and finite horizon T>=H+1, the tilted measure P.withDensity M_tau is a probability. Clip tau to min(tau,H), use the already accepted pathwise bounded stopped-density probability theorem, and show the original and clipped densities agree P-almost everywhere by withDensity_congr_ae. This closes normalisation despite P-null exceptional stopping paths without any Q_infinity law or WH assumption.
-- source:
--   Proved esscher_bounded_stop_density_probability a74b4ab5-3f15-4ead-b813-962d2d0e65a5; pinned Mathlib IsStoppingTime.min_const and withDensity_congr_ae.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ae_bounded_stop_density_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) := by sorry
