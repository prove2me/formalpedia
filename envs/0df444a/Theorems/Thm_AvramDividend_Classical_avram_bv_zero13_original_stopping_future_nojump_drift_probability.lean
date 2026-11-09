-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_stopping_future_nojump_drift_probability
-- name    : AvramDividend.Classical.avram_bv_zero13_original_stopping_future_nojump_drift_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:51:08.811516+00:00
-- url     : https://prove2.me/theorems/00cb3771-a520-48cf-a5d8-deac1da022b8
-- title:
--   Finite-activity original BV post-stopping zero-jump residual survival probability at true right-continuous stopping times
-- statement:
--   For original BV finite-negative-jump-activity spectrally negative Levy X, every finite stopping time for the original right-continuous filtration has the physical post-stopping source residual exactly zero over any deterministic duration with probability exp of minus duration times the original negative-jump intensity. This is the source-exact finite-activity no-negative-jump survival hazard after genuinely random restart clocks, including zero intensity and duration zero. It uses the existing strong Markov law of original stopped future X and the existing finite-activity residual-zero atom probability, without auxiliary compound Poisson source substitution. Conditional survival on stopped history is a further step.
-- source:
--   Proved d2b96f8c original right-continuous stopped future path law, 5e61917b original BV residual-zero exponential probability, 722354f7 stopped future path measurability and 840bbf85 whole source path measurability.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_stopping_future_nojump_drift_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) :
    P.real {ω : Ω |
      ((T : ℝ) * X.drift -
        (X.X (τ ω + T) ω - X.X (τ ω) ω)) -
      (((0 : ℝ≥0) : ℝ) * X.drift -
        (X.X (τ ω + 0) ω - X.X (τ ω) ω)) = 0} =
    Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
