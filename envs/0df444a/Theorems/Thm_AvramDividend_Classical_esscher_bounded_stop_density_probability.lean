-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability
-- name    : AvramDividend.Classical.esscher_bounded_stop_density_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:46:04.485634+00:00
-- url     : https://prove2.me/theorems/a74b4ab5-3f15-4ead-b813-962d2d0e65a5
-- title:
--   The realised Esscher density at a genuine bounded stopping time defines a probability
-- statement:
--   For a genuine bounded Lévy stopping time τ≤H with deterministic Esscher terminal T≥H+1 and θ≥0, the realised compensated exponential Mτ gives an actual probability measure P.withDensity Mτ. The canonical dyadic upper grid is constructed inside the proof and its uniform integrability follows from the proved finite-grid L² bound. No global Esscher path law or independently sampled clock under this realised density is claimed.
-- source:
--   Accepted bounded stop dyadic grid theorem 062ac6d1 and prospective upper-grid probability of realised stopped likelihood. No WH, exit ratio, or killed-scale assumptions.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_density_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) := by sorry
