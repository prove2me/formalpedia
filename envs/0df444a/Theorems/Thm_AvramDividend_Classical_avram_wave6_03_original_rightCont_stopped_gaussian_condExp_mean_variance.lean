-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:30:27.85167+00:00
-- url     : https://prove2.me/theorems/ee632d15-4ba9-47ec-acfd-165214fcc0c3
-- title:
--   Actual original stopped Gaussian increment has conditional mean zero and conditional variance h sigma squared
-- statement:
--   On the same original spectrally negative Levy probability space, under the zero-jump-measure hypothesis nu=0 and without requiring sigma>0, take an arbitrary bounded stopping time for the right-continuous original filtration. Its true drift-centred post-stopping increment Y=X.X_(tau+h)-X.X_tau-h*c is integrable, has conditional expectation zero given the stopped-history sigma algebra, and its integrable square has conditional expectation h*sigma^2. Establish the conditional statements from the already Proved independence of the entire actual post-stop increment path from the stopped history, the actual source stopped MemLp2 and exact mean and variance. This is a genuine random-stop martingale and quadratic compensator interface, not a separate Brownian process or general-nu bracket theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable Y P ∧
      (P[Y | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => Y ω ^ 2) P ∧
      (P[(fun ω => Y ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) := by
  sorry
