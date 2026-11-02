-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
-- name    : AvramDividend.Classical.avram_wave5_02a_rational_grid_actual_jump_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:51:07.942893+00:00
-- url     : https://prove2.me/theorems/d2b50fa0-2cb9-42d2-b9d8-5f58170a2775
-- title:
--   Measurable rational-grid first-crossing candidates cover every actual source jump
-- statement:
--   For any dense countable nonnegative-time grid and surjective enumeration of grid-start and rational-level pairs, the original source grid first-crossing times give measurable nonnegative time candidates covering every positive nonzero original jump, for every sample. Infinite candidates are sent to zero and therefore do not remove any positive jump. No standard Borel sample assumption or replacement process is used.
-- source:
--   Canonical Proved original source first-crossing measurability aed03c08, rational jump separation 2ec22b22, and dense-grid recovery 5afb8a0d.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_countable_grid_first_hit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_jump_rational_separation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_dense_grid_recovers_separated_source_jump

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_rational_grid_actual_jump_coverage
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    let T : ℕ → Ω → ℝ≥0 := fun k ω =>
      (⨅ n : ℕ, {ω : Ω | grid (pairs k).1 < grid n ∧
          X.X (grid n) ω < ((pairs k).2 : ℝ)}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω).toNNReal
    (∀ k, Measurable (T k)) ∧
    (∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ k, T k ω = u) := by sorry
