-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_countable_predictable_cell_lintegral_series
-- name    : AvramDividend.Classical.avram_p2_f_weighted_countable_predictable_cell_lintegral_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:08:40.362242+00:00
-- url     : https://prove2.me/theorems/e2625ff4-f5c1-48de-8e10-a5c0258a7d16
-- title:
--   Countably many predictable nonnegative marked cells inherit weighted first-moment compensation
-- statement:
--   For any countable family of nonnegative ambient-measurable marked counts and weights with individually established exact weighted first moments, the expected countable sum equals the countable sum of rate-weighted expected weights. No finite activity, integrability or Lévy ν-rate is postulated. This is the exact countable Tonelli extension of finite predictable rectangle compensation needed for original Lévy jump-measure integrands.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_tsum and Measurable.aemeasurable, with explicit individual moment assumption, suitable for P2-E.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_countable_predictable_cell_lintegral_series
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω)
    (N H : ι → Ω → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (hN : ∀ i, Measurable (N i))
    (hH : ∀ i, Measurable (H i))
    (hEach : ∀ i,
      (∫⁻ ω, H i ω * N i ω ∂μ) = (∫⁻ ω, H i ω ∂μ) * r i) :
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂μ) =
    ∑' i, (∫⁻ ω, H i ω ∂μ) * r i := by sorry
