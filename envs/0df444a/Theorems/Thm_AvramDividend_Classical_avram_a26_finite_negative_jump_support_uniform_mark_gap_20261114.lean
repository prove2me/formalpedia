-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_finite_negative_jump_support_uniform_mark_gap_20261114
-- name    : AvramDividend.Classical.avram_a26_finite_negative_jump_support_uniform_mark_gap_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:29:21.611816+00:00
-- url     : https://prove2.me/theorems/c4ef9c25-53b7-4df4-b59a-4ec63e4babac
-- title:
--   Uniform strictly positive magnitude gap for finite negative marked jump support
-- statement:
--   Every finite support of strictly negative jumps over a fixed finite horizon admits a single positive lower bound for the magnitude of each nonzero negative mark.
-- source:
--   Finite original jump support theorem 1e50b68a and finite-set minimum, conditional form.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite strictly negative jump support is uniformly separated from zero on every finite horizon. -/

theorem AvramDividend.Classical.avram_a26_finite_negative_jump_support_uniform_mark_gap_20261114
    (F : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hFinite : {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ F u ≠ 0}.Finite)
    (hNegative : ∀ u : ℝ≥0, 0 < u → u ≤ T → F u ≠ 0 → F u < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T → F u ≠ 0 → F u ≤ -ε := by sorry
