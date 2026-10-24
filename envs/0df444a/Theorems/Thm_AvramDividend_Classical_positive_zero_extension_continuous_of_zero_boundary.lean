-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_zero_extension_continuous_of_zero_boundary
-- name    : AvramDividend.Classical.positive_zero_extension_continuous_of_zero_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:44:26.200452+00:00
-- url     : https://prove2.me/theorems/53bc2f79-3fe4-4356-85be-dcf1ab8e5490
-- title:
--   A continuous positive-time function vanishing at zero has continuous zero extension
-- statement:
--   A real function continuous on the closed nonnegative half-line and vanishing at the origin has a globally continuous extension by zero on nonpositive times. The frontier of Ioi 0 is {0}, its closure is Ici 0, and Mathlib continuous_indicator provides the gluing principle.
-- source:
--   Mathlib continuous_indicator, frontier_Ioi and closure_Ioi.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Order.DenselyOrdered
open Set

theorem AvramDividend.Classical.positive_zero_extension_continuous_of_zero_boundary
    (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hg0 : g 0 = 0) :
    Continuous ((Ioi (0 : ℝ)).indicator g) := by sorry
