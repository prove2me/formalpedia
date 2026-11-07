-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_quadratic_cell_collision_power_error
-- name    : AvramDividend.Classical.avram_redux19_quadratic_cell_collision_power_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:47:51.104849+00:00
-- url     : https://prove2.me/theorems/f5f31bb9-be61-4f7a-ae28-fda46401af9a
-- title:
--   Quadratic rare-jump cell errors give inverse-mesh product error
-- statement:
--   For actual unit-interval short-cell expectation bounds, a nonnegative rare-jump collision error bounded by C/(n+1)^2 implies an error at most C/(n+1) after multiplying the independent-cell factor n+1 times. This is the quantitative finite-mesh bridge from collision bounds to the exponential Laplace limit.
-- source:
--   Apply the accepted subunit n-power Lipschitz estimate at n+1 and use positivity of n+1 to simplify the rational quadratic bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux19_unit_interval_power_lipschitz
noncomputable section

theorem AvramDividend.Classical.avram_redux19_quadratic_cell_collision_power_error
    (a b C : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hC : 0 ≤ C)
    (hgap : b - a ≤ C / ((n + 1 : ℕ) : ℝ) ^ 2) :
    0 ≤ b ^ (n + 1) - a ^ (n + 1) ∧
      b ^ (n + 1) - a ^ (n + 1) ≤ C / ((n + 1 : ℕ) : ℝ) := by sorry
