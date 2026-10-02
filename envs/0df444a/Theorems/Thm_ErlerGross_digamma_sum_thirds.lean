-- Prove2me | Theorems.Thm_ErlerGross_digamma_sum_thirds
-- name    : ErlerGross.digamma_sum_thirds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:50:30.809132+00:00
-- url     : https://prove2.me/theorems/aa462eda-60ed-45b3-b1d5-090449756c91
-- title:
--   Gauss digamma sum at thirds
-- statement:
--   The special case at denominator three of Gauss digamma multiplication states that the sum of the digamma values at one third and two thirds is twice the value at one, minus three times the natural logarithm of three.
-- source:
--   Gauss digamma multiplication formula, specialized to denominator 3.

import Mathlib

namespace ErlerGross
theorem digamma_sum_thirds :
    Complex.digamma ((1 : Complex) / 3) + Complex.digamma ((2 : Complex) / 3) =
      2 * Complex.digamma 1 - (3 : Complex) * (Real.log 3 : Complex) := by
  sorry
end ErlerGross
