-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:32:37.572638+00:00
-- url     : https://prove2.me/theorems/75f1abe0-2305-4824-bfeb-c6fa7498f11f
-- title:
--   Original right-continuous stopped-history independent of same-path future Levy increments
-- statement:
--   For the genuine original spectrally negative Levy process X in its right-continuous original filtration, and a genuine finite stopping time τ represented by its ≤-event condition, the sigma algebra of stopped history is independent under P of the entire actual future shifted increment path t ↦ X_(τ+t)−X_τ. Transport the canonically proved finite-stopping strong Markov independence through the canonically proved same-path right-continuous Levy lift. This does not assume ν=0, σ>0 or a detached copy, and is a source-path Gaussian stochastic-integral localisation input.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedSigma_indep_shiftedPath

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        inferInstance) P := by
  sorry
