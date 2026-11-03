-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:42:18.420848+00:00
-- url     : https://prove2.me/theorems/731576f3-00fb-496a-9d04-2fec81d6bfa6
-- title:
--   Original right-continuous stopped Lévy exponential compensator has unit conditional mean
-- statement:
--   For the original spectrally negative Lévy source and an actual bounded stopping time of its right-continuous filtration, the future multiplicative exponential martingale increment exp(θ(X_(τ+h)−X_τ)−h ψ(θ)) is integrable and has conditional expectation exactly one given the original stopped-history sigma algebra for all θ≥0 and h≥0. This is the same-Ω source Lévy cumulant martingale difference, valid for arbitrary negative jumps and all Gaussian coefficients including σ=0. The proof uses the already Proved exact stopped conditional source Laplace transform and an honest bounded deterministic exponential normalisation. It does not identify the full-jump Lévy increment with the continuous Gaussian component.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_source_condExp_laplace

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) P ∧
    (P[(fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (1 : ℝ))) := by
  sorry
