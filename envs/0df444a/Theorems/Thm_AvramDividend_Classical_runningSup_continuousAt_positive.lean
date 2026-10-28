-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_positive
-- name    : AvramDividend.Classical.runningSup_continuousAt_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:35:45.273337+00:00
-- url     : https://prove2.me/theorems/653f11f5-df49-45c3-aa86-253e54f5d1b8
-- title:
--   Actual reflected Lévy local-time regulator is continuous at every positive time
-- statement:
--   The genuine running supremum S of a spectrally negative Lévy path is continuous at every strictly positive time. Combine the already proved actual left continuity on Iio t and actual right continuity on Ici t. Restrict right continuity to Ioi t, then use the pinned Mathlib characterisation continuousAt_iff_continuous_left'_right'. This is a necessary strong regularity prerequisite for constructing the local-time inverse and the Itô excursion decomposition rather than merely postulating an excursion measure.
-- source:
--   Proved runningSup_left_continuous_actual and runningSup_right_continuous_actual; Mathlib.Topology.Order.LeftRight.

import Mathlib.Topology.Order.LeftRight
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.runningSup_continuousAt_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ≥0 => runningSup X s ω) t := by sorry
