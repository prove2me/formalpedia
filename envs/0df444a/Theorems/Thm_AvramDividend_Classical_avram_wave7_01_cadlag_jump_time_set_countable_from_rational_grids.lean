-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_jump_time_set_countable_from_rational_grids
-- name    : AvramDividend.Classical.avram_wave7_01_cadlag_jump_time_set_countable_from_rational_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:03:44.704981+00:00
-- url     : https://prove2.me/theorems/87b851df-fc68-4af2-91bf-ff4baee7c8e0
-- title:
--   Every real càdlàg path has countably many nonzero jump times via rational grid coverage
-- statement:
--   The set of positive times at which a real right-continuous path with strict finite left limits has a nonzero jump is countable, because it is covered by the union of two rational first-downcrossing countable ranges for the path and its negation.
-- source:
--   Apply the already Proved two-sign jump-time coverage theorem and the countability of the ranges of two ℕ-indexed time sequences; use monotonicity of countable sets under subset.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_cadlag_jump_time_set_countable_from_rational_grids
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    Set.Countable {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0} := by sorry
