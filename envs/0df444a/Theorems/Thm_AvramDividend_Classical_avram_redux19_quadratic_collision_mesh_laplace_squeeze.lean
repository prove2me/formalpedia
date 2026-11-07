-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_quadratic_collision_mesh_laplace_squeeze
-- name    : AvramDividend.Classical.avram_redux19_quadratic_collision_mesh_laplace_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:08:30.706486+00:00
-- url     : https://prove2.me/theorems/ebc3f7a3-9d66-4457-9fe5-b9ed8b42a22f
-- title:
--   Quadratic single-cell errors preserve the exact mesh Laplace limit
-- statement:
--   If the actual short-cell exponential factor is between zero and its linearised Levy mark-loss factor and differs from it by at most a quadratic collision error C/(n+1)^2, its n+1-fold product converges to exp(-x). This combines exact original-collision estimates with the analytic exponential limit; arbitrary x is admissible whenever the stated all-n cell hypotheses hold.
-- source:
--   Apply the accepted quadratic collision product bound; squeeze the product error to zero using the pinned const-div/n limit and compose the accepted shifted-mesh exponential convergence with subtraction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux19_quadratic_cell_collision_power_error
import Theorems.Thm_AvramDividend_Classical_avram_redux19_shifted_mesh_exp_limit
open Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_redux19_quadratic_collision_mesh_laplace_squeeze
    (x C : ℝ) (a : ℕ → ℝ)
    (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, 0 ≤ a n)
    (hab : ∀ n : ℕ, a n ≤ 1 - x / ((n : ℝ) + 1))
    (hb : ∀ n : ℕ, 1 - x / ((n : ℝ) + 1) ≤ 1)
    (hgap : ∀ n : ℕ, (1 - x / ((n : ℝ) + 1)) - a n ≤ C / (((n + 1 : ℕ) : ℝ) ^ 2)) :
    Tendsto (fun n : ℕ => a n ^ (n + 1)) atTop (𝓝 (Real.exp (-x))) := by sorry
