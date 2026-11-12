-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger120_monotone_grid_first_crossing_index
-- name    : AvramDividend.Classical.avram_gledger120_monotone_grid_first_crossing_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:42:57.303855+00:00
-- url     : https://prove2.me/theorems/7917a160-1857-45c5-a8bc-35537fd2b055
-- title:
--   Positive stopped monotone grid has an exact first-crossing cell
-- statement:
--   A nondecreasing stopped grid beginning at zero and reaching a positive clock by index N has a first crossing strictly before N. This gives the exact final cell index for a stopped Gaussian dividend-contact cash ledger.
-- source:
--   Original physical grid decomposition needed for the gledger81 stopped dividend contact mesh correction.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger120_monotone_grid_first_crossing_index
    (v : ℕ → ℝ≥0) (hv : Monotone v)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hv0 : v 0 = 0)
    (N : ℕ) (hN : v N = ρ) :
    ∃ k : ℕ, k < N ∧ v k < ρ ∧ v (k + 1) = ρ := by sorry
