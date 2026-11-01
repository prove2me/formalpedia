-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
-- name    : AvramDividend.Classical.avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:24:32.340396+00:00
-- url     : https://prove2.me/theorems/2d63fe5c-fbfd-4cb9-b934-8ee040f38abe
-- title:
--   Original stopped marked finite-grid compensated prefix is measurable with respect to the later past
-- statement:
--   If past sigma-algebras increase across a finite deterministic grid, future marked cell sigma-fields are included in later pasts, and each stopped coefficient and marked cell increment is strongly measurable in its respective sigma-field, then the finite compensated prefix is strongly measurable in the later past. This is the adaptedness step needed for genuine finite-grid martingale conditional expectations; no compensator identity or martingale conclusion is assumed.
-- source:
--   Pinned Mathlib 0df444a StronglyMeasurable.mono, StronglyMeasurable.mul, Finset.stronglyMeasurable_sum.

import Mathlib

open MeasureTheory

theorem AvramDividend.Classical.avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (mPast mFuture : ℕ → MeasurableSpace Ω)
    (hPastMono : Monotone mPast)
    (hFuturePast : ∀ i n, i < n → mFuture i ≤ mPast n)
    (H Z : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[mPast i] (H i))
    (hZ : ∀ i, StronglyMeasurable[mFuture i] (Z i))
    (n : ℕ) :
    StronglyMeasurable[mPast n]
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by sorry
