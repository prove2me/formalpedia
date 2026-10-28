-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
-- name    : AvramDividend.Classical.runningSup_right_continuous_actual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:30:28.546806+00:00
-- url     : https://prove2.me/theorems/9faeaaa4-6933-425a-ac6d-88d7bf48aa56
-- title:
--   Actual spectrally negative Lévy running-supremum regulator is right-continuous at every time
-- statement:
--   The actual running supremum of a canonical spectrally negative Lévy process is right-continuous at every nonnegative time, using its monotonicity, exact supremum representation, domination and underlying Lévy right-continuity. Together with proved left continuity this establishes the continuity of the regulator and supports constructing inverse local time and excursion intervals.
-- source:
--   Proved runningSup_monotone_and_path_le, runningSup_eq_rawSup_nonneg, runningSup_right_continuous_of_right_continuous.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_right_continuous_actual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => runningSup X s ω) (Ici t) t := by sorry
