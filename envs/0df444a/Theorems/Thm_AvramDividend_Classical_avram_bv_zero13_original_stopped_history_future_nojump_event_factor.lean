-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_stopped_history_future_nojump_event_factor
-- name    : AvramDividend.Classical.avram_bv_zero13_original_stopped_history_future_nojump_event_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:55:02.120453+00:00
-- url     : https://prove2.me/theorems/004fdd62-ca5e-4f3e-978d-7f3b12dc4f4d
-- title:
--   Original finite activity BV future no-jump event independent of arbitrary stopped-history event
-- statement:
--   For the original BV finite activity spectrally negative Levy source and any finite right-continuous stopping time, the physical post-stopping zero-drift-deficit event over any fixed future duration is independent of every event measurable at the stopped history. The result is a same-original-filtration event factorisation for all adapted restarts and supplies the predictable first-negative-jump hazard when combined with original stopped future exponential survival. No auxiliary process or artificial stopping-clock floor is assumed.
-- source:
--   Proved 75f1abe0 original right-continuous stopped-history versus stopped future path independence; 722354f7 stopped future path measurability; Mathlib indepSet_iff_measure_inter_eq_mul and stoppedHistory_event_measurable.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_stopped_history_future_nojump_event_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0)
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A) :
    P (A ∩ {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0}) =
      P A * P {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0} := by sorry
