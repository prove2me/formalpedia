-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_grid_count_pathwise_liminf_implies_expected_liminf
-- name    : AvramDividend.Classical.avram_p2_grid_count_pathwise_liminf_implies_expected_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:12:44.234994+00:00
-- url     : https://prove2.me/theorems/8922f86a-694f-488e-86a8-771435dc606c
-- title:
--   Fatou transfer from pathwise mesh liminf bound to original mean jump count
-- statement:
--   For any actual samplewise jump count and its measurable refining-grid counts on the same measured sample space, if the jump count is bounded by the pointwise liminf of grid counts then its expectation is bounded by the liminf of grid expectations. It applies the pinned Mathlib Fatou lemma; does not assume jump compensators, intensity or stochastic rate and is the analytic expectation bridge from the independently Proved actual-path jump-to-grid liminf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_grid_count_pathwise_liminf_implies_expected_liminf
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (jumpCount : Ω → ℝ≥0∞) (grid : ℕ → Ω → ℝ≥0∞)
    (hgrid : ∀ n, Measurable (grid n))
    (hBound : ∀ ω, jumpCount ω ≤
      Filter.liminf (fun n => grid n ω) Filter.atTop) :
    (∫⁻ ω, jumpCount ω ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, grid n ω ∂P) Filter.atTop := by sorry
