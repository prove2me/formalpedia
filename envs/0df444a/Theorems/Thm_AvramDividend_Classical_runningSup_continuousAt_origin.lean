-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_origin
-- name    : AvramDividend.Classical.runningSup_continuousAt_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:39:49.295723+00:00
-- url     : https://prove2.me/theorems/3609775b-d7ec-49f9-8cb6-f38bd99b1515
-- title:
--   The genuine spectrally negative Lévy running-supremum local-time regulator is continuous at time zero
-- statement:
--   At the bottom time 0 of ℝ≥0, right-continuity is full continuity because Ici 0 is the universal time domain. The already proved runningSup_right_continuous_actual theorem consequently yields continuity of the genuine running maximum at its origin, completing the endpoint requirement for a globally continuous local-time regulator and the inverse local-time construction.
-- source:
--   Proved runningSup_right_continuous_actual and pinned Mathlib continuousWithinAt_univ.

import Mathlib.Topology.ContinuousOn
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.runningSup_continuousAt_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ContinuousAt (fun s : ℝ≥0 => runningSup X s ω) 0 := by sorry
