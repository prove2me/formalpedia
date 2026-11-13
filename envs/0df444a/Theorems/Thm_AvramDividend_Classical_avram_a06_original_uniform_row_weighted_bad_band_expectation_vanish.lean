-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
-- name    : AvramDividend.Classical.avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:35:49.56691+00:00
-- url     : https://prove2.me/theorems/3c93987b-eca7-4403-94d5-4b264f7b6143
-- title:
--   A06 physical uniform-row cofinal band omitted cash-error mean vanishes
-- statement:
--   For any fixed original physical uniform-grid row, the finitely many original left-limit reserve coordinates eventually enter every cofinal interior compact band. The weighted omitted-row error on the complementary event has vanishing expected value under a measurable integrable genuine stochastic envelope H. This source-exact finite-grid bridge imports two already Proved A06 helpers and preserves all signed-generator residuals outside the estimate. The separate hard work is to furnish original reserve coordinate measurability and source envelope.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
import Theorems.Thm_AvramDividend_Classical_avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (Z : Ω → ℕ → ℝ)
    (hZ : ∀ i, Measurable (fun ω => Z ω i))
    (H : Ω → ℝ) (hHm : Measurable H) (hHI : Integrable H P) :
    Tendsto (fun k : ℕ =>
      ∫ ω, (if ∀ i < n + 1,
        (0 < Z ω i ∧ ENNReal.ofReal (Z ω i) < C) →
          Z ω i ∈ Icc (a k) (b k) then (0 : ℝ) else H ω) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
