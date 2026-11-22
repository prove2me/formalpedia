-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_future_indep_fullPast
-- name    : AvramDividend.Classical.avram_lsc_realTime_future_indep_fullPast
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:40:56.77048+00:00
-- url     : https://prove2.me/theorems/f7993add-5548-4f1e-b214-37c45dcaf7c5
-- title:
--   Real-time original centred Lévy increment independent of its entire prior source path
-- statement:
--   For nonnegative real start time, the original Lévy process past path up to that start time is independent of the original centred Gaussian-scaled increment over the subsequent real-time interval. This is the path-level past-future independence required by the imported LevyStochCalc BrownianMotion joint-increment-independent field.
-- source:
--   Pinned Avram to LevyStochCalc Brownian source filtration interface. Uses proved Avram real-time increment independence theorem 8d9862cd-21d0-4741-98ee-a75a7b294b58 and original SpectrallyNegativeLevy.adapted/filtration monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_realTime_future_indep_fullPast
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap
        (fun ω : Ω => fun u : Set.Iic (Real.toNNReal s) => X.X u ω)
        inferInstance)
      (MeasurableSpace.comap (fun ω =>
        ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
          (t - s) * X.c) / X.σ) inferInstance) P := by sorry
