-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger123_clipped_uniform_grid_reaches_stop_by_final_index
-- name    : AvramDividend.Classical.avram_gledger123_clipped_uniform_grid_reaches_stop_by_final_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:48:12.765696+00:00
-- url     : https://prove2.me/theorems/1f31c568-009e-49ba-8e7c-e9c627c58328
-- title:
--   Original uniform clipped grid equals the stopping clock by index m+2
-- statement:
--   The final endpoint of an original positive-horizon uniformly clipped stopped dividend grid is the original stopped time, provided that time is no later than the horizon. This closes the finite-index existence input for the first-crossing cash ledger.
-- source:
--   Original Gaussian gledger81 stopped dividend-contact mesh-correction crossing-index existence.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger123_clipped_uniform_grid_reaches_stop_by_final_index
    (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    v (m + 2) = ρ := by sorry
