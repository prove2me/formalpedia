-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB278_bad_dividend_grid_time_union_le_inverse_mesh_variation
-- name    : AvramDividend.Classical.avram_gbB278_bad_dividend_grid_time_union_le_inverse_mesh_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:52:13.021242+00:00
-- url     : https://prove2.me/theorems/56ac893c-8ed6-46f5-978b-b1c805e90bc2
-- title:
--   Original dividend grid bad-cell time union bounded by inverse refinement times total variation
-- statement:
--   For every monotone real dividend sequence sampled on a fourth-power physical mesh and positive refinement m, the Lebesgue volume of the union of bad cells, whose dividend increment exceeds the inverse cube of m, is at most ENNReal.ofReal of total dividend variation divided by m. This exactly combines the finite-union volume bound B277 and the adapted dividend-monotonicity count B267; the original finite-cap localized occupation theorem B274 needs precisely this bad-cell contribution, separate from the good-cell Gaussian small-ball probability.

import Mathlib
open MeasureTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB278_bad_dividend_grid_time_union_le_inverse_mesh_variation (d : ℕ → ℝ) (hd : Monotone d) (n m : ℕ) (hm : 0 < m)
:
    volume (⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
       (fun i => 1 / ((m : ℝ) ^ 3) < d (i + 1) - d i)),
      Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4)))) ≤
      ENNReal.ofReal ((d (n * m ^ 4) - d 0) / (m : ℝ)) := by sorry
