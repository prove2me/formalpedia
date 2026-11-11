-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite56_cap_fraction_cutoff_tendsto
-- name    : AvramDividend.Classical.avram_gfinite56_cap_fraction_cutoff_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:48:53.917774+00:00
-- url     : https://prove2.me/theorems/ee953e75-e72b-4c16-bf44-682c01d6ee91
-- title:
--   Finite-cap rational cutoffs converge to the cap
-- statement:
--   The standard cofinal rational cap cutoff b_j = c (j+1)/(j+2) converges to c. This deterministic convergence is needed in the original finite-cap Gaussian positive-residual diagonal and its cap-strip occupation error.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite56_cap_fraction_cutoff_tendsto (c : ℝ) :
    Tendsto (fun j : ℕ => c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) atTop (𝓝 c) := by
  sorry
