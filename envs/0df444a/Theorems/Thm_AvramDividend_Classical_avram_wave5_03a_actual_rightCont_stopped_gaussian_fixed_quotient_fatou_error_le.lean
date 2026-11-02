-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:28:23.960193+00:00
-- url     : https://prove2.me/theorems/64ae5b54-9278-47c4-bc15-762c55725619
-- title:
--   Actual stopped Gaussian increment lies within fixed exponential quotient variance excess
-- statement:
--   For the original source X with nu=0 and bounded right-continuous stopping time, the actual pathwise stopped drift-centred increment Y has nonnegative squared difference to the genuine same-path fixed exponential-martingale quotient Z(theta). Fatou and the Proved exact source quotient distance limit bound its lintegral by (exp(h sigma² theta²)-1)/theta²-h sigma². This crucial authentic source L2 estimate is the bridge to exact variance convention and continuous Ito, with sigma=0 allowed, no copied Brownian and no claim about jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_quotient_pointwise_drift_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_distance_limit

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P) ≤
      ENNReal.ofReal (((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) /
        θ ^ 2) - (h : ℝ) * X.σ ^ 2) := by
  sorry
