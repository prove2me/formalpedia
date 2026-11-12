-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger91_monotone_clipped_grid_first_crossing_index
-- name    : AvramDividend.Classical.avram_gledger91_monotone_clipped_grid_first_crossing_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:12:25.679623+00:00
-- url     : https://prove2.me/theorems/8ca1da98-622b-4ad4-b07f-c2bdefdff681
-- title:
--   Any monotone grid starting below and ending at the stopped clock has a first crossing cell
-- statement:
--   For a monotone finite nonnegative time grid that begins below a stopping clock and reaches the clock at index N, there exists a first crossing cell k<N ending exactly at the clock with a strictly earlier start. This index enables exact separation of active interior, ruin/horizon crossing, and inactive clipped cells in gledger81.
-- source:
--   Genuine finite-grid first-crossing decomposition required for original Gaussian gledger81 16e988d7; combines with gledger89 exact grid exhaustion and gledger90 cash partition.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger91_monotone_clipped_grid_first_crossing_index
    (v : ℕ → ℝ≥0) (hv : Monotone v) (ρ : ℝ≥0)
    (hv0 : v 0 < ρ) (N : ℕ) :
    v N = ρ → ∃ k : ℕ, k < N ∧ v k < ρ ∧ v (k + 1) = ρ := by sorry
