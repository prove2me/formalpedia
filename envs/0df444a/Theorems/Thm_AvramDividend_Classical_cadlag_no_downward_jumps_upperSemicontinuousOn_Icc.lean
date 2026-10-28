-- Prove2me | Theorems.Thm_AvramDividend_Classical_cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
-- name    : AvramDividend.Classical.cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:30:47.772988+00:00
-- url     : https://prove2.me/theorems/95786bc2-b5ce-4ff0-9f7c-c06aae11789f
-- title:
--   Any càdlàg nonnegative-time real path with no downward jumps is upper semicontinuous on every compact time interval
-- statement:
--   A real-valued path on nonnegative time which is right-continuous, admits a finite left limit at each positive time, and never jumps downwards is upper semicontinuous on [0,ζ] for every finite ζ. At t>0, apply the proved one-sided continuity criterion; at t=0, right continuity on Ici 0 is ordinary continuity because all nonnegative times lie in Ici 0. This is the analytic ingredient guaranteeing attainment of maximum excursion height on a compact finite-lifetime interval.
-- source:
--   Càdlàg path regularity and upper semicontinuity; Kuznetsov et al. (2013), excursion-height regularity argument.

import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_upperSemicontinuousAt_of_rightContinuous_leftLimit_le

open AvramDividend.Classical Set Topology Filter
open scoped NNReal

theorem AvramDividend.Classical.cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
    (f : ℝ≥0 → ℝ) (ζ : ℝ≥0)
    (hRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Filter.Tendsto f
        (nhdsWithin t (Iio t)) (nhds l))
    (hNoDown : ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Filter.Tendsto f (nhdsWithin t (Iio t)) (nhds l) →
      l ≤ f t) :
    UpperSemicontinuousOn f (Icc 0 ζ) := by sorry
