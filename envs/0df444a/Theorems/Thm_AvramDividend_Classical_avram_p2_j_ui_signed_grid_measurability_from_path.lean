-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_signed_grid_measurability_from_path
-- name    : AvramDividend.Classical.avram_p2_j_ui_signed_grid_measurability_from_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:25:00.694527+00:00
-- url     : https://prove2.me/theorems/7a26c899-9286-4102-8b37-afc2d2b7097b
-- title:
--   Measurable real test of finite source-grid increments is strongly measurable from each measurable path coordinate
-- statement:
--   For a real process whose fixed-time coordinates are measurable and a Borel measurable real test, prove every signed finite n+1 grid sum is strongly measurable under any measure. This supplies the exact measurable-grid hypothesis for P2-J source-specific Vitali without assuming any jump-rate law, compensator, or grid-to-jump limit.

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_signed_grid_measurability_from_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hXm : ∀ t : ℝ≥0, Measurable (X t))
    (g : ℝ → ℝ) (hgm : Measurable g)
    (h : ℕ → ℝ) :
    ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1),
        g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal (h n)) ω -
           X ((i : ℝ≥0) * Real.toNNReal (h n)) ω)) P := by sorry
