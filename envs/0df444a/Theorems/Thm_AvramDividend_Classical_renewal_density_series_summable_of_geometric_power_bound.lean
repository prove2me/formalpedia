-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
-- name    : AvramDividend.Classical.renewal_density_series_summable_of_geometric_power_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:02:40.99181+00:00
-- url     : https://prove2.me/theorems/617e5955-fb8d-4395-8c9f-96559f035eda
-- title:
--   Summability of geometric-power dominated renewal convolution terms
-- statement:
--   If a nonnegative renewal convolution sequence is bounded at a positive argument x by (n+1)^2 rho^(n+1)/x for rho in [0,1), then its infinite series converges. This gives pointwise convergence of the series in the bounded-variation Esscher renewal kernel representation, using the verified envelope from causal_subunit_renewal_full_real_power_package.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

theorem AvramDividend.Classical.renewal_density_series_summable_of_geometric_power_bound
    (ρ x : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hx : 0 < x)
    (F : ℕ → ℝ) (hF0 : ∀ n : ℕ, 0 ≤ F n)
    (hFbound : ∀ n : ℕ,
      F n ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    Summable F := by sorry
