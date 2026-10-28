-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_exponential_halfline_integral
-- name    : AvramDividend.Classical.chat04_positive_discount_exponential_halfline_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:46:32.251024+00:00
-- url     : https://prove2.me/theorems/aa24d789-a001-474a-9e67-85a61d015e76
-- title:
--   Positive-discount Laplace integral of a constant time reward
-- statement:
--   Evaluate the normalising real exponential kernel integral on the positive time half-line as 1/p. The identity is the scalar component of the time-Laplace transform needed to identify a constant killed-scale expectation from its resolvent.
-- source:
--   Pinned Mathlib integral_exp_mul_Ioi, with positive discount and zero lower endpoint.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem AvramDividend.Classical.chat04_positive_discount_exponential_halfline_integral (p : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t))) = 1 / p := by sorry
