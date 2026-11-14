-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB288_fourth_power_gaussian_good_cell_aggregate_bound
-- name    : AvramDividend.Classical.avram_gbB288_fourth_power_gaussian_good_cell_aggregate_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:06:32.789193+00:00
-- url     : https://prove2.me/theorems/d20039fb-b6f6-4cbd-9ac8-bcbeb2fbc6b3
-- title:
--   Finite Gaussian good-cell integral estimates sum to twice the horizon over mesh refinement
-- statement:
--   Given one integrated Gaussian density bound per fourth-power physical mesh cell, finite-sum monotonicity and the Proved B281 source kernel identity yield a total bound of 2n/m. This is the quantitative aggregation step used to sum the B266 original-source Gaussian good-cell hit probabilities within the B276b finite-cap fixed-level occupation estimate.

import Mathlib
open MeasureTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_gbB288_fourth_power_gaussian_good_cell_aggregate_bound (n m : ℕ) (hm : 0 < m) (f : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.range (n * m ^ 4),
      f i ≤ (1 / ((m : ℝ) ^ 3)) *
        (∫ t in ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))..
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
          (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)))) :
    (∑ i ∈ Finset.range (n * m ^ 4), f i) ≤
      2 * (n : ℝ) / (m : ℝ) := by sorry
