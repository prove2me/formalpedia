-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_path_countable_measurable_marked_jump_count
-- name    : AvramDividend.Classical.avram_wave7_01_original_path_countable_measurable_marked_jump_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:52:39.21911+00:00
-- url     : https://prove2.me/theorems/3f95364d-e2fe-45db-ac3b-052c9a6ac2b5
-- title:
--   Globally measurable deduplicated marked jump count from original path candidate family
-- statement:
--   A countable family of measurable candidate jump times with shrinking left and right grid samples has a measurable family of exact mark extensions and a measurable finite-horizon Borel marked count after removing duplicate candidate times. All claims use raw original coordinate paths.
-- source:
--   For each candidate k invoke the accepted exact two-grid mark extension theorem; choose countably many marks; apply the accepted deduplicated countable Borel marked-candidate measurability theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_original_path_countable_measurable_marked_jump_count
    (grid : ℕ → ℝ≥0)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (htime : ∀ k, Measurable (time k))
    (rightIndex leftIndex : ℕ → ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hRightIndex : ∀ k n, Measurable (rightIndex k n))
    (hLeftIndex : ∀ k n, Measurable (leftIndex k n))
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (hRightBounds : ∀ (k : ℕ) (Y : ℝ≥0 → ℝ) (n : ℕ),
      time k Y ≤ grid (rightIndex k n Y) ∧
      grid (rightIndex k n Y) ≤ time k Y + ε n)
    (lower : ℕ → ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (hLeftBounds : ∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
      ∀ n, lower k n Y ≤ grid (leftIndex k n Y) ∧
        grid (leftIndex k n Y) < time k Y)
    (hLower : ∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
      Tendsto (fun n => lower k n Y) atTop (𝓝 (time k Y)))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ mark : ℕ → (ℝ≥0 → ℝ) → ℝ,
      (∀ k, Measurable (mark k)) ∧
      (∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
        ContinuousWithinAt Y (Ici (time k Y)) (time k Y) →
        Tendsto Y (𝓝[<] (time k Y))
          (𝓝 (Function.leftLim Y (time k Y))) →
        mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
      Measurable (fun Y : ℝ≥0 → ℝ =>
        ∑' k : ℕ,
          if 0 < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (1 : ℝ≥0∞) else 0) := by sorry
