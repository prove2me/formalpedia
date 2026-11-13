-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a26_grid_eventually_beyond_strict_stop
-- name    : AvramDividend.Classical.avram_ga_a26_grid_eventually_beyond_strict_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:23:04.870332+00:00
-- url     : https://prove2.me/theorems/bad2eb49-ad79-4b27-9b89-7b45bc912977
-- title:
--   Uniform rational mesh eventually exceeds every strict pre-horizon stopping time
-- statement:
--   For any strictly earlier nonnegative stopping time r<n, the final-but-one grid point m*n/(m+1) eventually lies to the right of r. This is the deterministic foundation of almost-sure vanishing of the stopped Gaussian terminal cell on paths with rho<n.
-- source:
--   Avram Gaussian A26 strict-stop terminal mesh

import Mathlib

theorem AvramDividend.Classical.avram_ga_a26_grid_eventually_beyond_strict_stop
    (n r : ℝ) (hr0 : 0 ≤ r) (hrn : r < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      r ≤ (m : ℝ) * (n / ((m : ℝ) + 1)) := by sorry
