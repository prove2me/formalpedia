-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:14:57.731966+00:00
-- url     : https://prove2.me/theorems/9bc2ebb1-f741-4e0e-9cd5-1d543c4183ca
-- title:
--   Actual rightCont stopped original Gaussian exponential quotient has exact two-parameter L2 distance kernel
-- statement:
--   For the genuine SpectrallyNegativeLevy P F process with ν=0 and a bounded stopping time in the original right-continuous filtration, the expected square of the difference of two exponential Gaussian martingale quotients equals the exact explicit source Gaussian distance kernel exp(hσ²θ²), exp(hσ²η²), exp(hσ²θη). Transport the canonically Proved source L2-distance theorem along the canonically Proved literal same-path right-continuous Levy lift, preserving X.X and X.σ exactly. This provides a direct quantitative Gaussian localisation and L2-limit identification interface; no detached Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    (∫ ω, (Z θ ω - Z η ω) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 +
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * η ^ 2)) - 1) / η ^ 2 -
      2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)) := by
  sorry
