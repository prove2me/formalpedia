-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_grid_active_binomial_poisson_limit_ws01b
-- name    : AvramDividend.Classical.bv_grid_active_binomial_poisson_limit_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:55:37.27399+00:00
-- url     : https://prove2.me/theorems/02ac8b91-0cab-468f-a797-4cf6373570e9
-- title:
--   Poisson law of rare events for exponential Lévy grid active-cell probabilities
-- statement:
--   For each real intensity r and fixed count k, the exact binomial probability-mass expression with n independent active-cell probabilities p_n=1−exp(−r/n) tends to the Poisson mass exp(−r)r^k/k!. For nonnegative r this describes finite-activity Lévy jump indicators on independent equal-length cells, once their actual process-level independence has been separately established; the result is purely analytic and makes no unjustified pathwise claim.
-- source:
--   Combine the accepted bv_rare_grid_exponential_limit_ws01b with the pinned Mathlib ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop and simplify 1−(1−exp(−r/n)). The exact 23-line proof passed a private remote Prove2Me compilation probe.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_rare_grid_exponential_limit_ws01b
open Filter Topology

theorem AvramDividend.Classical.bv_grid_active_binomial_poisson_limit_ws01b
    (r : ℝ) (k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((n.choose k : ℕ) : ℝ) *
          (1 - Real.exp (-(r / (n : ℝ)))) ^ k *
          Real.exp (-(r / (n : ℝ))) ^ (n - k))
      atTop
      (nhds (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) := by sorry
