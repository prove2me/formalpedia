-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_frequently_bad_source_grid_cells_impossible
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_frequently_bad_source_grid_cells_impossible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:46:28.985201+00:00
-- url     : https://prove2.me/theorems/ad9b6be4-092f-4d41-af44-88bd303913f2
-- title:
--   Finitely many genuine large jumps rule out frequently spurious large original grid cells
-- statement:
--   For any triangular source grid of shrinking cells on compact time horizon, assume finite F contains all genuine source jumps of magnitude ≥ρ>0 and every cell avoids F. Prove it is impossible that arbitrarily late grid rows contain a cell increment ≥ρ. Extract a cofinal sequence of bad rows, choose one offending cell per row and apply the proved source-specific no-spurious contradiction. No Lévy rate or compensator premise.

import Mathlib
open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_frequently_bad_source_grid_cells_impossible
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℕ → ℝ≥0) (w : ℕ → ℝ≥0)
    (haT : ∀ n i, a n i ≤ T)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbw : ∀ n i, b n i ≤ a n i + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
       ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (havoid : ∀ n i, ∀ t ∈ F, ¬ (a n i < t ∧ t ≤ b n i))
    (hbad : ∃ᶠ n in (atTop : Filter ℕ),
      ∃ i, ρ ≤ |Y (b n i) - Y (a n i)|) :
    False := by sorry
