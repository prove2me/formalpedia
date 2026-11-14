-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB281_fourth_power_gaussian_total_good_cell_time_kernel
-- name    : AvramDividend.Classical.avram_gbB281_fourth_power_gaussian_total_good_cell_time_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:41:51.063091+00:00
-- url     : https://prove2.me/theorems/641c723e-f54a-4145-abb6-b7468c9af267
-- title:
--   Exact total Gaussian good-cell integrated time kernel across a fourth-power refinement mesh
-- statement:
--   For the physical time mesh with n m^4 cells of width 1/m^4, the sum over cells of their inverse-cube dividend threshold times the integral of elapsed time to power minus one-half equals precisely 2n/m. This exact analytic estimate is the cumulative Gaussian good-cell cost entering original source B274 localized prescribed-level occupation. It follows from the per-cell translated inverse-square-root integral B280 and the fourth-power mesh scaling B279.

import Mathlib
open MeasureTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_gbB281_fourth_power_gaussian_total_good_cell_time_kernel (n m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (n * m ^ 4),
      (1 / ((m : ℝ) ^ 3)) *
        (∫ t in ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))..
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
          (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)))) =
      2 * (n : ℝ) / (m : ℝ) := by sorry
