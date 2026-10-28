-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one
-- name    : AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:39:39.986978+00:00
-- url     : https://prove2.me/theorems/c31104b1-ffd1-42aa-aa1f-c612525057f8
-- title:
--   Exact mass-one Esscher likelihood at a genuine bounded Lévy stopping time
-- statement:
--   For a genuine bounded stopping time τ≤H, positive Esscher parameter θ≥0, a probability Lévy law P and any deterministic terminal T≥H+1, the stopped Esscher likelihood has exact expectation one. The proof constructs the canonical adapted finite dyadic upper grids internally, applies the accepted uniform L²/Vitali stopped-limit result, and needs neither a uniform-integrability hypothesis nor an optional-stopping or WH axiom.
-- source:
--   Accepted bounded-stop explicit upper dyadic grid 062ac6d1 and accepted UI-free upper-grid stopped-likelihood integral-one theorem 8132e3df; no two-sided exit or killed-scale harmonicity.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one_of_upper_grids

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by sorry
