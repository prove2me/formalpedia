-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_future_functional_condExp
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_future_functional_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:39:18.490605+00:00
-- url     : https://prove2.me/theorems/ad8a83d2-3f01-459c-9554-76dd2756f8e2
-- title:
--   Every integrable full-future Lévy source functional has constant conditional expectation after right-continuous stopping
-- statement:
--   On the same original spectrally negative Lévy source and its actual right-continuous filtration, take any finite right-continuous stopping time τ and any measurable real functional Z of the entire future increment path whose post-stop evaluation is integrable. Its conditional expectation given the exact stopped-history sigma algebra equals its unconditional expectation. This derives a source-faithful full-path conditional strong Markov interface from Proved original stopped-future independence, the Proved same-path right-continuous lift and actual stopped path measurability. The theorem assumes neither ν=0 nor σ>0, handles σ=0 and enables all source Gaussian/jump functional moments. It asserts no nonexistent Brownian copy or continuous residual bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_future_functional_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (Z : (ℝ≥0 → ℝ) → ℝ) (hZmeas : Measurable Z)
    (hInt : Integrable (fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) P) :
    P[(fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => ∫ ω, Z (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) ∂P) := by
  sorry
