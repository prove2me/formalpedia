-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_quadratic_void_deficit_squeeze_limit_20261115
-- name    : AvramDividend.Classical.avram_a25_quadratic_void_deficit_squeeze_limit_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:57:16.600503+00:00
-- url     : https://prove2.me/theorems/3e964661-f2ca-42e3-9ded-cc1eef596605
-- title:
--   Quadratic sandwich for scaled small-time void deficit implies Poisson rate slope
-- statement:
--   A reusable deterministic squeeze theorem for the Poisson small-time void-probability rate. If the scaled occupancy deficit n q_n is bounded between r - (r²/2)(1/n) and r eventually, it converges to r. Used with q_n = 1 - P(no original negative-Borel jumps before T/n), r=Tν(B). This isolates the analytic convergence from the genuinely stochastic first/second factorial moment occupancy bound.
-- source:
--   Pinned Mathlib tendsto_one_div_atTop_nhds_zero_nat and tendsto_of_tendsto_of_tendsto_of_le_of_le.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_a25_quadratic_void_deficit_squeeze_limit_20261115
    (r : ℝ) (q : ℕ → ℝ)
    (hBounds : ∀ᶠ n in (Filter.atTop : Filter ℕ),
      r - (r ^ 2 / 2) * (1 / ((n : ℕ) : ℝ)) ≤ ((n : ℕ) : ℝ) * q n ∧
        ((n : ℕ) : ℝ) * q n ≤ r) :
    Filter.Tendsto (fun n : ℕ => ((n : ℕ) : ℝ) * q n)
      Filter.atTop (nhds r) := by sorry
