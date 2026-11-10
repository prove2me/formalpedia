-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:43:42.630039+00:00
-- url     : https://prove2.me/theorems/ce77d378-6cd1-443b-9d1e-26abd9fedf7d
-- title:
--   Every Borel observable of the original shifted Lévy increments is independent of the stopped original past
-- statement:
--   On the actual SpectrallyNegativeLevy sample space, every Borel real functional of the full post-stopping-time original X increment path is independent of the original rightCont stopped-time sigma-algebra. Transfer the Proved full shifted-source independence 75f1abe0 through the measurable functional using comap monotonicity. This is a legitimate same-source ingredient for the Gaussian residual increment martingale and jump cross-orthogonality once the exact shift-covariant physical jump-mass identity is proved. No independent Brownian or auxiliary law is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (W : (ℝ≥0 → ℝ) → ℝ) (hW : Measurable W) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω => W (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω))
        inferInstance) P := by sorry
