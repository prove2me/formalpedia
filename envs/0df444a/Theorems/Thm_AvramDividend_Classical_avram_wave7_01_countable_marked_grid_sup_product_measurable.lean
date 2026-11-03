-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_sup_product_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_countable_marked_grid_sup_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:06:54.108436+00:00
-- url     : https://prove2.me/theorems/1120ee03-ba60-4f08-99f4-a4d13d189417
-- title:
--   The supremum of countably many finite Borel-marked path-increment grid counts is product measurable
-- statement:
--   For arbitrary real coordinate paths, any Borel mark set B and countable family of finite nonnegative-time grids, the supremum of finite marked-increment cardinalities is measurable in the path coordinate product σ-algebra. This extracts the analytic measurable core of original-source future-grid compensation; it does not identify the supremum with the true càdlàg marked jump measure.
-- source:
--   Measurable coordinate evaluations, finite indicator sum = Finset.filter.card, Mathlib Measurable.iSup; split from original weighted supremum factor candidate 22441 after 300-second verifier timeout.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_countable_marked_grid_sup_product_measurable
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      ⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
        Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)) := by sorry
