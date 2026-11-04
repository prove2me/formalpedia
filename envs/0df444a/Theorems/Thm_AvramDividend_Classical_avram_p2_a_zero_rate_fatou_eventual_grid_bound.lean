-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_fatou_eventual_grid_bound
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_fatou_eventual_grid_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:39:28.821812+00:00
-- url     : https://prove2.me/theorems/364a0e01-1990-4eca-83fb-588f33bcdb3b
-- title:
--   Fatou and eventual grid mean bound control actual separated-jump expectations
-- statement:
--   For a measured sample space and measurable nonnegative grid counts, any pointwise actual jump-count ≤ ENNReal liminf(grid) together with an eventual uniform upper bound M on expected grid counts yields expected jump count ≤ M. This combines the previously Proved Fatou transfer with the pinned Filter.liminf_le_of_le theorem and makes the original-process finite-mean step explicit, without asserting a Lévy rate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_grid_count_pathwise_liminf_implies_expected_liminf

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_fatou_eventual_grid_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (jumpCount : Ω → ℝ≥0∞) (grid : ℕ → Ω → ℝ≥0∞)
    (hgrid : ∀ n, Measurable (grid n))
    (hPoint : ∀ ω, jumpCount ω ≤
      Filter.liminf (fun n => grid n ω) Filter.atTop)
    (M : ℝ≥0∞)
    (hBound : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, grid n ω ∂P) ≤ M) :
    (∫⁻ ω, jumpCount ω ∂P) ≤ M := by sorry
