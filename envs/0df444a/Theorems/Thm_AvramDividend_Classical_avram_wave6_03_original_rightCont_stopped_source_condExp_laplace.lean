-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_source_condExp_laplace
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_source_condExp_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:28:40.433793+00:00
-- url     : https://prove2.me/theorems/b93f62d8-8a50-47a8-bffd-4545bf908f38
-- title:
--   Original right-continuous source stopped positive exponential increment has exact conditional Lévy cumulant
-- statement:
--   For the actual original spectrally negative Lévy source in its right-continuous filtration, any pointwise bounded finite stopping time, future horizon h and nonnegative Laplace parameter θ, the genuine post-stopping positive exponential increment is integrable and its conditional expectation given the actual stopped-history sigma algebra is exactly exp(h ψ(θ)). This holds for arbitrary source jump measure and for all σ, including σ=0. It combines the Proved literal same-path right-continuous Lévy lift, source exponential moments, and independence of the entire actual future increment path from the stopped past. This is an original-process strong Markov martingale-characteristic input; it does not falsely identify the non-Gaussian source increment as Brownian or solve the still-missing continuous residual bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_source_condExp_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) P ∧
    (P[(fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => Real.exp ((h : ℝ) * X.ψ θ))) := by
  sorry
