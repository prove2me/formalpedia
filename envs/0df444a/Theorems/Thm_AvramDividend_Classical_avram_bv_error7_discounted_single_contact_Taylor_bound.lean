-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_discounted_single_contact_Taylor_bound
-- name    : AvramDividend.Classical.avram_bv_error7_discounted_single_contact_Taylor_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:23:55.262833+00:00
-- url     : https://prove2.me/theorems/d4f8d1c4-0e07-46b0-add8-563107e480b4
-- title:
--   Discounted final contact C1 Taylor error controlled by one compensated cell increment
-- statement:
--   If the original value function has a Lipschitz bound for the two endpoints of the final physical-grid contact cell and the starting derivative is bounded, its discounted Taylor remainder is controlled by twice that Lipschitz constant times the compensated Y increment.
-- source:
--   Direct triangle inequality, discounted exponential <=1 for q,u>=0, and value/derivative bounds. This is a reusable analytic estimate for proving a.e. contact remainder convergence from compensated BV source-mesh convergence without imposing differentiability at the endpoint.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_discounted_single_contact_Taylor_bound
    (w : ℝ → ℝ) (q u z c L : ℝ)
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hLip : |w (z + c) - w z| ≤ L * |c|)
    (hDeriv : |deriv w z| ≤ L) :
    |Real.exp (-(q * u)) *
        (w (z + c) - w z - deriv w z * c)| ≤
      (2 * L) * |c| := by sorry
