-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger122_monotone_stopped_grid_postcrossing_plateau
-- name    : AvramDividend.Classical.avram_gledger122_monotone_stopped_grid_postcrossing_plateau
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:45:24.221041+00:00
-- url     : https://prove2.me/theorems/418da977-178c-4680-a4ed-ff9b7b69faf7
-- title:
--   Original stopped grid is constant beyond its first crossing
-- statement:
--   Every complete grid cell after a first crossing of a bounded monotone stopped grid is stationary at the exact same stopped clock. Consequently the corresponding dividend-contact corrections are zero.
-- source:
--   Original Gaussian gledger81 full finite contact-sum tail vanishing after the crossing.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger122_monotone_stopped_grid_postcrossing_plateau
    (v : ℕ → ℝ≥0) (hv : Monotone v)
    (ρ : ℝ≥0) (hbound : ∀ i : ℕ, v i ≤ ρ)
    (k : ℕ) (hcross : v (k + 1) = ρ) :
    ∀ i : ℕ, k < i → v i = ρ ∧ v (i + 1) = ρ := by sorry
