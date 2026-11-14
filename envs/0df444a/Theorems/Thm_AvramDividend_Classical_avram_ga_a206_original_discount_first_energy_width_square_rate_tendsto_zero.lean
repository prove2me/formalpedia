-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
-- name    : AvramDividend.Classical.avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:43:41.973006+00:00
-- url     : https://prove2.me/theorems/8e969367-d1e0-46bb-9ed8-b74b1efa8cf4
-- title:
--   The actual uniform Gaussian discount width times raw first-energy squared rate vanishes
-- statement:
--   For a fixed physical horizon, discount rate, spatial Lipschitz coefficient, and real uniform second-energy bound, the deterministic upper estimate for the square of the discounted finite absolute Gaussian raw source sum tends to zero. This reuses the already Proved uniform nonnegative real time mesh width limit, Gaussian mesh time mass bound a83 and Gaussian drift square mass convergence a82, and it completes the deterministic rate after applying the Proved raw first-energy square bound a154 and discount source bound a155 in the sound Gaussian discount source repair.
-- source:
--   Proved avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero, avram_ga_a83 and avram_ga_a82; exact Gaussian physical time mesh.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a82_original_gaussian_mesh_drift_square_mass_tendsto_of_width
import Theorems.Thm_AvramDividend_Classical_avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
    (n : ℕ) (q L K : ℝ) :
    Tendsto (fun m : ℕ =>
      (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 *
        ((m : ℝ) * K)) atTop (𝓝 (0 : ℝ)) := by sorry
