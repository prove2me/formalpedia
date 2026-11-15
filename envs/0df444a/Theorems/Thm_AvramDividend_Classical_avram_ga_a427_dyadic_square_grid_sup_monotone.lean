-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a427_dyadic_square_grid_sup_monotone
-- name    : AvramDividend.Classical.avram_ga_a427_dyadic_square_grid_sup_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T23:49:26.374251+00:00
-- url     : https://prove2.me/theorems/3fe3a836-64c4-4b2e-b8f0-38e1573f414f
-- title:
--   Dyadic sampled squared finite maximum is monotone under grid refinement
-- statement:
--   When the dyadic time grid is refined by doubling the number of cells, every previous grid point remains sampled, and the maximum of the squared observations cannot decrease.
-- source:
--   Elementary dyadic grid refinement and finite supremum monotonicity; no probabilistic hypotheses required.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a427_dyadic_square_grid_sup_monotone
    {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Monotone (fun k : ℕ =>
      (Finset.range (2^k + 1)).sup' (by simp)
        (fun i => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) := by sorry
