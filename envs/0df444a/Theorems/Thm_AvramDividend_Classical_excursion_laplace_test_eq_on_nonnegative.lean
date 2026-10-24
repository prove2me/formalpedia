-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_laplace_test_eq_on_nonnegative
-- name    : AvramDividend.Classical.excursion_laplace_test_eq_on_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:56:17.335817+00:00
-- url     : https://prove2.me/theorems/7bcc478c-782b-4ec8-a77f-ad786d6c991e
-- title:
--   Capped full-line Laplace test agrees with the original kernel on nonnegative support
-- statement:
--   For any real Laplace parameter s, the full-line bounded test using max(x,0) agrees exactly with exp(-s x) at every nonnegative x. Together with a support-zero-on-negatives condition, this identifies the weak-convergence test with the desired Laplace transform in the Esscher excursion resolvent measure limit.
-- source:
--   Elementary max identity for the finite-measure weak-limit construction, companion to excursion_laplace_test_continuous_bounded.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem AvramDividend.Classical.excursion_laplace_test_eq_on_nonnegative (s x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-(s * max x 0)) = Real.exp (-(s * x)) := by sorry
