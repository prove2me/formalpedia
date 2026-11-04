-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_strict_grid_indicator_liminf_le_closed_grid_liminf
-- name    : AvramDividend.Classical.avram_p2_34dbea70_strict_grid_indicator_liminf_le_closed_grid_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:36:40.138936+00:00
-- url     : https://prove2.me/theorems/d01758fd-d6c3-4ff2-a973-18686c11f07f
-- title:
--   Strict negative grid count means are bounded by closed-band grid count means
-- statement:
--   For any original or generic real-valued increment grid, every strict negative-threshold cell indicator is no larger than its closed-threshold indicator. Summing, integrating and taking liminf preserves this inequality, enabling a genuine original Lévy closed-tail grid expectation bound to control the strict indicators used to capture negative càdlàg jumps without a continuity or atomlessness assumption.

import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_strict_grid_indicator_liminf_le_closed_grid_liminf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℕ → ℕ → Ω → ℝ) (a : ℝ) (C : ℝ≥0∞)
    (hmean : Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        (Iic a).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (u n i ω) ∂P)
          atTop ≤ C) :
    Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
        (if u n i ω < a then (1 : ℝ≥0∞) else 0) ∂P)
        atTop ≤ C := by sorry
