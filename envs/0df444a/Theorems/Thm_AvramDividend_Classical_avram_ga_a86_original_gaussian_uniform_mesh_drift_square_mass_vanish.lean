-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish
-- name    : AvramDividend.Classical.avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:03:59.790748+00:00
-- url     : https://prove2.me/theorems/e0766b47-8a08-4436-880f-eba1c580fb45
-- title:
--   Exact original Gaussian uniform physical source drift squared mesh mass tends to zero
-- statement:
--   On the original Gaussian uniform physical grid with horizon natural n, for every real Lévy source drift c the total m-fold squared deterministic source increment drift (n/(m+1)*c)² converges to zero.
-- source:
--   Direct original b0d9951c raw-centred Gaussian stopped cross L1 ga_a81 deterministic drift mass from ga_a82 and ga_a83.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish (n : ℕ) (c : ℝ) :
    Tendsto (fun m : ℕ =>
      (m : ℝ) *
        (((((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * c)^2))
        atTop (𝓝 (0 : ℝ)) := by sorry
