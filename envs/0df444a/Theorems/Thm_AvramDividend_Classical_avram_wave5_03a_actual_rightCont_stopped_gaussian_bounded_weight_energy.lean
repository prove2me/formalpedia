-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weight_energy
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weight_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:36:41.533869+00:00
-- url     : https://prove2.me/theorems/d5f63862-1edb-41ef-99b0-e344f966b40f
-- title:
--   Exact same-source bounded Gaussian weight second moment bound with sigma squared
-- statement:
--   For the genuine source Gaussian Levy process with ν=0 and any original right-continuous bounded stopping time, a strongly measurable multiplier with |H|≤K has squared quotient energy bounded by K² (exp(h σ² θ²)-1)/θ² for θ≥0. This is a source-specific actual stopped weighted L2 energy bound in the precise sigma variance convention, from the canonical samepath cross moment, not an independent Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weight_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    let Z : Ω → ℝ := fun ω =>
      (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ
    (∫ ω, (H ω * Z ω) ^ 2 ∂P) ≤
      K ^ 2 * ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1) / (θ * θ)) := by
  sorry
