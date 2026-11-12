-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
-- name    : AvramDividend.Classical.avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:32:16.630166+00:00
-- url     : https://prove2.me/theorems/3a03c777-1f71-4d16-b9d6-e5f528e9a86a
-- title:
--   Clipped stopped mesh has strict interior cells and constant post-crossing tail
-- statement:
--   For a positive clock bounded by the horizon, the actual deterministic clipped grid has one first crossing cell. All earlier next endpoints are strictly pre-stop and every subsequent grid value equals the clock. This supplies exactly the chronological index hypotheses of the Proved gledger99 contact bound, gledger97 contact-tail cancellation and gledger95 cash partition.
-- source:
--   Original Gaussian gledger81 pathwise stopped contact proof needs a single index k with exact strict-prefix and constant-tail properties. This child combines already Proved gledger89 and gledger91 and proves only finite mesh geometry.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
import Theorems.Thm_AvramDividend_Classical_avram_gledger91_monotone_clipped_grid_first_crossing_index
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
    (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 2 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by sorry
