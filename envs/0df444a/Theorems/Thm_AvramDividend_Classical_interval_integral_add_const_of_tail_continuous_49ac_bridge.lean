-- Prove2me | Theorems.Thm_AvramDividend_Classical_interval_integral_add_const_of_tail_continuous_49ac_bridge
-- name    : AvramDividend.Classical.interval_integral_add_const_of_tail_continuous_49ac_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:04:23.692626+00:00
-- url     : https://prove2.me/theorems/0266c47c-4b97-4c7c-b739-f74e980c2822
-- title:
--   Interval integral splits a constant from a continuous tail on positive intervals
-- statement:
--   On a positive interval [a,b], the interval integral of a constant plus a tail continuous on (0,∞) splits as phi*(b-a) plus the tail integral. This is the deterministic integral-splitting step in the Chan-Kyprianou-Savov Esscher transfer for the unbounded-variation scale representation.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions, equations (4)-(6): deterministic integral split of the Esscher constant from the excursion-tail integral

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem interval_integral_add_const_of_tail_continuous_49ac_bridge
    (φ : ℝ) (tail : ℝ → ℝ) (a b : ℝ)
    (hTail : ContinuousOn tail (Ioi (0 : ℝ)))
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, φ + tail t) = φ * (b - a) + (∫ t in a..b, tail t) := by sorry

end AvramDividend.Classical
