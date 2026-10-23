-- Prove2me | Theorems.Thm_AvramDividend_Classical_log_derivative_nonintegrable_of_positive_vanishing
-- name    : AvramDividend.Classical.log_derivative_nonintegrable_of_positive_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T20:43:31.967257+00:00
-- url     : https://prove2.me/theorems/1eb4de79-8072-4751-8488-b0d180a626cf
-- title:
--   A positive differentiable function vanishing at zero has nonintegrable logarithmic derivative
-- statement:
--   A positive function V on positive real arguments tends to zero from the right at the origin and is differentiable at every positive point. Its real logarithm tends to negative infinity, so the absolute value of the logarithm tends to positive infinity. By the Mathlib nonintegrability theorem for derivatives of divergent functions along a one-sided filter, the derivative of log V is not Lebesgue integrable on (0,infinity). The chain rule identifies that derivative with V prime divided by V, which proves the conclusion. No local absolute continuity assumption is required. This gives the exact analytic implication needed by the unbounded Esscher tilted log-derivative origin target.

import Mathlib.Analysis.SpecialFunctions.NonIntegrable

open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem AvramDividend.Classical.log_derivative_nonintegrable_of_positive_vanishing
    (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x)
    (hzero : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    ¬ IntegrableOn (fun x : ℝ => deriv V x / V x) (Ioi (0 : ℝ)) := by sorry
