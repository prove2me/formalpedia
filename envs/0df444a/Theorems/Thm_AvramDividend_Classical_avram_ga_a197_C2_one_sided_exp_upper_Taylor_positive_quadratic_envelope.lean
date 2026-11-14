-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a197_C2_one_sided_exp_upper_Taylor_positive_quadratic_envelope
-- name    : AvramDividend.Classical.avram_ga_a197_C2_one_sided_exp_upper_Taylor_positive_quadratic_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:40.313211+00:00
-- url     : https://prove2.me/theorems/858341cc-8055-4fc0-be82-1274b0df2d62
-- title:
--   Positive Gaussian C2 Taylor source remainder has an exponential endpoint plus quadratic raw increment upper envelope
-- statement:
--   For a twice differentiable value function w whose value, first derivative and second iterated derivative at the stopped prepayment reserve are bounded by M, and whose value at the raw physical endpoint has a one-sided exponential upper bound, the positive part of the second-order classical Taylor remainder is bounded by that endpoint exponential plus M times one, raw absolute increment, and half the raw squared increment. This is the missing deterministic large-raw-increment envelope for a149; combine Proved gledger65 (or a73) and original stopped compact C2 a165 before using weighted Gaussian Chernoff tails.
-- source:
--   Pointwise C2 source jet absolute bounds and one-sided exponential value upper bound; no artificial Brownian surrogate.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a197_C2_one_sided_exp_upper_Taylor_positive_quadratic_envelope
    (w : ℝ → ℝ) (y r θ K M : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hw : |w y| ≤ M)
    (hderiv : |deriv w y| ≤ M)
    (hsecond : |iteratedDeriv 2 w y| ≤ M)
    (hupper : w (y + r) ≤ K * Real.exp (θ * (y + r))) :
    max (w (y + r) - w y - deriv w y * r -
        iteratedDeriv 2 w y / 2 * r^2) 0 ≤
      K * Real.exp (θ * (y + r)) +
        M * (1 + |r| + r^2 / 2) := by sorry
