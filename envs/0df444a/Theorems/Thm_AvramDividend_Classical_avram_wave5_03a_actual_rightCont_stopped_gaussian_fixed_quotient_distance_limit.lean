-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_distance_limit
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_distance_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:52:50.404194+00:00
-- url     : https://prove2.me/theorems/d707f14b-4d7a-4e35-8d2e-49c0c8a7bc92
-- title:
--   Exact original rightCont stopped Gaussian fixed-quotient L2 distance has variance-excess limit
-- statement:
--   For the original zero-jump Gaussian Lévy process stopped at bounded original right-continuous-filtration τ, fix θ>0. The real expected square of the same-path exponential martingale quotient difference Zθ-Z_{sqrt ε} tends, as ε↓0, to (exp(hσ²θ²)-1)/θ²-hσ². It follows from accepted same-source exact L2 distance and cross/energy limits. This provides a non-detached Gaussian quantitative intermediate for proving that the actual stopped drift-centred increment is the L2 limit, and subsequently zero-mean.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_fixed_parameter_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_quotient_L2_distance_exact

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_distance_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun ε : ℝ => (∫ ω,
        (Z θ ω - Z (Real.sqrt ε) ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) /
        θ ^ 2) - (h : ℝ) * X.σ ^ 2)) := by
  sorry
