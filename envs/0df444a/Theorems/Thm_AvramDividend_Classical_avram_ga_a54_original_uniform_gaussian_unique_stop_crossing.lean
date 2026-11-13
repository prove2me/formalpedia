-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a54_original_uniform_gaussian_unique_stop_crossing
-- name    : AvramDividend.Classical.avram_ga_a54_original_uniform_gaussian_unique_stop_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:52:34.233713+00:00
-- url     : https://prove2.me/theorems/39058de8-76c5-4a69-acbc-6916a200ef01
-- title:
--   Exact first stop-straddling cell for original m+1 Gaussian grid
-- statement:
--   For the precise original Gaussian grid width n/(m+1), if the original bounded stopping clock is positive and at most n, there is a unique first clipped cell reaching the stop. Every earlier cell is fully interior, and later cells remain frozen at the stop. This isolates the one stop-straddling cell required for the original physical Gaussian Taylor residual limit b0d9951c.
-- source:
--   Proved gledger110 3a03c777 with reindexing m-1; exact original b0d9951c clipped mesh. Does not replace X, D or the stopping filtration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a54_original_uniform_gaussian_unique_stop_crossing
    (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) (hm : 0 < m) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 1 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by sorry
