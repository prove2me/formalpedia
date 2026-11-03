-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_strict_downjumps_countably_rational_enumerable
-- name    : AvramDividend.Classical.avram_wave7_01_cadlag_strict_downjumps_countably_rational_enumerable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:02:06.994628+00:00
-- url     : https://prove2.me/theorems/96023774-c388-4940-88ec-08a03f920346
-- title:
--   Every strict downward càdlàg jump occurs in a countable measurable rational-grid first-hit enumeration
-- statement:
--   For any right-continuous real path with strict left limits and only negative nonzero jumps, every positive jump time equals one of a fixed countable sequence of rational-threshold first-downcrossing infima. Combine the Proved rational neighbourhood separator with the stronger every-prior-grid-start exact downcrossing theorem. This is the exact pathwise coverage required for a countable measurable marked jump enumerator for the genuine original source Lévy process.
-- source:
--   New analytic first-hit separation theorem 3cb3ca42 and all-prior-start stronger dense-grid infimum theorem; no source measure replacement or hidden finite-activity assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_cadlag_strict_downjumps_countably_rational_enumerable
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hDown : ∀ u : ℝ≥0, 0 < u →
      Y u - Function.leftLim Y u ≠ 0 →
      Y u < Function.leftLim Y u)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    let T : ℕ → ℝ≥0 := fun k =>
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧
          Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal
    ∀ u : ℝ≥0, 0 < u →
      Y u - Function.leftLim Y u ≠ 0 →
      ∃ k : ℕ, T k = u := by sorry
