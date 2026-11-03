-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:41:53.228497+00:00
-- url     : https://prove2.me/theorems/ed9c2972-f4d4-4a04-bc86-8fea84570ea3
-- title:
--   Countable rational first-downcrossing candidate-time enumeration is jointly product-measurable
-- statement:
--   For a real path with the raw coordinate-product measurable structure and fixed countable time grid, all exact first visits below rational levels after enumerated grid starts form a measurable countable sequence of candidate times. Every coordinate is a countable infimum of measurable piecewise constants. This is a deterministic path-space ingredient for the intrinsic original Lévy process; no unrelated random process is introduced.
-- source:
--   Adapt the previously Proved source first-crossing grid measurability aed03c08 and the new marked first-hit singleton hB technique; measurable_pi_lambda and ENNReal.measurable_toNNReal.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
    (grid : ℕ → ℝ≥0) (pairs : ℕ → ℕ × ℚ) :
    Measurable (fun Y : ℝ≥0 → ℝ => fun k : ℕ =>
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧
          Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal) := by sorry
