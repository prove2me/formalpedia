-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
-- name    : AvramDividend.Classical.avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:52:35.973495+00:00
-- url     : https://prove2.me/theorems/eadc9439-8bb2-4cb1-8a5f-e61ff7f75418
-- title:
--   All real càdlàg jumps lie in two countable rational first-downcrossing families
-- statement:
--   Any finite nonzero jump of an arbitrary right-continuous real path with all strict-left limits occurs either among rational first-downcrossing candidate times of the path or of its pointwise negation. This removes the global spectrally-negative jump assumption for deterministic marked-jump extraction.
-- source:
--   Split the nonzero jump into negative or positive sign; negative invokes local downjump coverage on Y; positive invokes it on -Y using continuous negation and left-limit negation at strictly positive time.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_local_strict_downjump_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_left_limit_negation_at_positive_time

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    ∀ u : ℝ≥0, 0 < u →
      Y u - Function.leftLim Y u ≠ 0 →
      (∃ k : ℕ,
        (⨅ n : ℕ,
          {Z : ℝ≥0 → ℝ |
            grid (pairs k).1 < grid n ∧
            Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
            (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal = u) ∨
      (∃ k : ℕ,
        (⨅ n : ℕ,
          {Z : ℝ≥0 → ℝ |
            grid (pairs k).1 < grid n ∧
            Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
            (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤)
            (fun v : ℝ≥0 => -Y v)).toNNReal = u) := by sorry
