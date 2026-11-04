-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean
-- name    : AvramDividend.Classical.avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:45:46.045732+00:00
-- url     : https://prove2.me/theorems/4f270bf9-32a4-4f50-a04e-ac4982ec9240
-- title:
--   Fatou transfers a genuine jump-count liminf bound to its expected count
-- statement:
--   For an arbitrary measure P, intrinsic nonnegative count g, and sequence f of measurable finite-grid nonnegative counts, if g is pointwise bounded by liminf f and liminf of the grid means is bounded by C, then the expected intrinsic count is at most C. The proof uses Mathlib's genuine liminf Fatou inequality, avoiding integrability assumptions and keeping ENNReal infinity. This deterministic/probabilistic interface will transport the original Lévy pathwise grid bounds to first-moment estimates without assuming a Lévy jump intensity.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : Ω → ℝ≥0∞) (f : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hpath : ∀ ω, g ω ≤ Filter.liminf (fun n => f n ω) atTop)
    (hmean : Filter.liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop ≤ C) :
    (∫⁻ ω, g ω ∂P) ≤ C := by sorry
