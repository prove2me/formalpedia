-- Prove2me | Theorems.Thm_AvramDividend_Classical_upperSemicontinuousAt_of_rightContinuous_leftLimit_le
-- name    : AvramDividend.Classical.upperSemicontinuousAt_of_rightContinuous_leftLimit_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:51:35.861521+00:00
-- url     : https://prove2.me/theorems/3f20ea52-0e3f-470e-88a2-7c3568b064e4
-- title:
--   Right continuity and a left limit no larger than the current value imply upper semicontinuity at positive time
-- statement:
--   For a real path on nonnegative times, at a strictly positive time t, if the path is continuous from the right, admits a left limit l, and has no downward jump there (l≤f(t)), then it is upper semicontinuous at t. For any y>f(t), the left limit and right continuity provide neighbourhoods restricted to (-∞,t) and [t,∞) where f<y. Those two neighbourhood filters join to the ordinary neighbourhood filter because the two time half-lines cover the space. This is a fundamental analytic step towards showing reflected spectrally negative Lévy excursions attain their finite-lifetime maximal height.
-- source:
--   Elementary topology of càdlàg paths with no negative jumps and upper semicontinuity; Kuznetsov-Kyprianou-Rivero (2013), Lemma 2.4's excursion-height hitting-time argument.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.upperSemicontinuousAt_of_rightContinuous_leftLimit_le
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hRight : ContinuousWithinAt f (Ici t) t)
    (l : ℝ)
    (hLeft : Filter.Tendsto f (nhdsWithin t (Iio t)) (nhds l))
    (hle : l ≤ f t) :
    UpperSemicontinuousAt f t := by sorry
