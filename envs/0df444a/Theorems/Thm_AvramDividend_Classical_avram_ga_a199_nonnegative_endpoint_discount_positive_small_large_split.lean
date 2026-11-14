-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a199_nonnegative_endpoint_discount_positive_small_large_split
-- name    : AvramDividend.Classical.avram_ga_a199_nonnegative_endpoint_discount_positive_small_large_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:26:03.0216+00:00
-- url     : https://prove2.me/theorems/f37781c4-4610-4459-ae5c-7ec767814f71
-- title:
--   Positive discount mismatch splits into local Lipschitz small increments and a compact start-value bound for large increments
-- statement:
--   Let a be a nonnegative discount decrement bounded by Q, v the source value at a compact stopped reserve, and u the value at the raw prepayment endpoint. When u is nonnegative and v≤M, the positive part of the negative discount decrement times u-v is bounded on small raw increments by Q times the local Lipschitz constant times the increment magnitude; on large increments it is bounded by Q times M. This is the needed pointwise source estimate for a sound Gaussian discount-positive L1 alternative to a151 when the actual barrier value has a nonnegative endpoint, unlike the unrestricted formal hypotheses of a151.
-- source:
--   Discount monotonicity and small-large case split, with explicit one-sided value-function lower bound.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a199_nonnegative_endpoint_discount_positive_small_large_split
    (a Q v u r δ L M : ℝ)
    (ha : 0 ≤ a) (hQa : a ≤ Q)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hu : 0 ≤ u) (hv : v ≤ M)
    (hSmall : |r| < δ → |u - v| ≤ L * |r|) :
    max (-a * (u - v)) 0 ≤
      Q * (if |r| < δ then L * |r| else M) := by sorry
