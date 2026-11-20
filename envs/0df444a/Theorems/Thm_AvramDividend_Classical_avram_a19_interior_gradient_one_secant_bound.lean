-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_interior_gradient_one_secant_bound
-- name    : AvramDividend.Classical.avram_a19_interior_gradient_one_secant_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:51:10.932615+00:00
-- url     : https://prove2.me/theorems/ca4a2295-a0e8-4ffb-8e49-abe0278a3853
-- title:
--   Interior HJB derivative ≥1 gives dividend secant slope
-- statement:
--   On any original reserve interval [y,z] below the finite cap, continuity up to endpoints, interior differentiability and the HJB slope condition deriv w>=1 imply w(z)-w(y)>=z-y. This is the missing exact calculus bridge to the proved cap-linear above-cap payment cell lemma, allowing correct original finite-cap right dividend jumps. The stochastic Gaussian/jump Itô and ruin-contact limits are independent obligations.
-- source:
--   Finite-cap original stopped HJB dividend slope: monotonicity of w(t)-t on a closed interval by nonnegative derivative.

import Mathlib
open Set

/-- An HJB interior derivative at least one yields the exact dividend secant inequality. -/
theorem AvramDividend.Classical.avram_a19_interior_gradient_one_secant_bound
    (w : ℝ → ℝ) (y z : ℝ) (hyz : y ≤ z)
    (hcont : ContinuousOn w (Icc y z))
    (hdiff : DifferentiableOn ℝ w (Ioo y z))
    (hgrad : ∀ t ∈ Ioo y z, 1 ≤ deriv w t) :
    z - y ≤ w z - w y := by sorry
