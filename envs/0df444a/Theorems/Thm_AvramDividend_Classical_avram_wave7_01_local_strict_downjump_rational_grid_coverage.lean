-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_local_strict_downjump_rational_grid_coverage
-- name    : AvramDividend.Classical.avram_wave7_01_local_strict_downjump_rational_grid_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:29:38.172217+00:00
-- url     : https://prove2.me/theorems/7923eaf8-1f3b-4f9c-9694-5477829bfb48
-- title:
--   A single strict downward càdlàg jump lies in rational first-downcrossing enumeration without global jump-sign assumptions
-- statement:
--   Every locally strict downward jump at positive time on any right-continuous path with left limits is found by the universal countable enumeration of rational threshold/grid starting point first downcrossings. No assumption on the sign of other jumps is required. This is the analytic strengthening necessary to enumerate both signs on general real càdlàg paths.
-- source:
--   Re-use the Proved rational neighbourhood separator and all-prior-start dense-grid exact downcrossing at the selected down-jump; choose its enumerating pair and convert the extended-nonnegative infimum back to time.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_local_strict_downjump_rational_grid_coverage
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    let T : ℕ → ℝ≥0 := fun k =>
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧
          Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal
    ∀ u : ℝ≥0, 0 < u →
      Y u < Function.leftLim Y u →
      ∃ k : ℕ, T k = u := by sorry
