-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration
-- name    : AvramDividend.Classical.avram_ws01h_lowerPassage_stopping_rightCont_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:46:44.008985+00:00
-- url     : https://prove2.me/theorems/a1d326c3-53d7-4e5e-a317-0ce98468d3ff
-- title:
--   Original strict lower-passage time is stopping in the right-continuous Levy filtration
-- statement:
--   For the actual source Lévy process and every real lower barrier, the infimum of strict below-barrier passage times is a stopping time in the right-continuous version of its original filtration. This permits source-faithful comparison with the first-upcrossing stopping time, making the killed lower-survival past event observable at that upper record. It does not require a scale function, Esscher path-law construction, or the desired two-sided exit formula.
-- source:
--   Avram–Palmowski–Pistorius (2007), equation (3.6) strict exit clocks; already-Proved lowerCrossingClock_lt_horizon_iff_exists_witness 07415c4f and levy_lowerCrossing_before_filtration_measurable 335dd834. Apply the same right-continuous stopping-time criterion as independently Proved upperPassage_stopping_rightCont_filtration 72dac635. Independent noncircular prerequisite for 5bcf90e1.

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_lowerPassage_stopping_rightCont_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) :
    IsStoppingTime 𝓕.rightCont (twoSidedExitDownTime X lower) := by sorry
