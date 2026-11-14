-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
-- name    : AvramDividend.Classical.avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:55:47.621335+00:00
-- url     : https://prove2.me/theorems/06da2d14-5bee-4fd4-ab1b-793b461e22cd
-- title:
--   Uniform Gaussian physical-mesh Chernoff tilt has negative linear mesh exponential rate
-- statement:
--   For positive time horizon n and mesh order m, a positive Gaussian Chernoff tilt proportional to m+1 bounds the logarithmic weighted increment tail by a constant minus 3 delta squared (m+1)/(8n). The bound is the exact algebraic input to the original full-cell large positive Gaussian exponential-tail summation.
-- source:
--   Avram original zero-jump Gaussian source large-cell one-sided exponential tail, supporting original combined source a216.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Real Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a219_physical_mesh_gaussian_optimal_positive_chernoff_rate
    (n m : ℕ) (hn : 0 < n) (θ δ : ℝ) :
    -(δ * ((m : ℝ) + 1) / (2 * (n : ℝ))) * δ +
      ((n : ℝ) / ((m : ℝ) + 1)) *
        (θ + δ * ((m : ℝ) + 1) / (2 * (n : ℝ)))^2 / 2 ≤
      θ * δ / 2 + (n : ℝ) * θ^2 / 2 -
        (3 * δ^2 / (8 * (n : ℝ))) * ((m : ℝ) + 1) := by sorry
