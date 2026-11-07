-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_scaled_signed_source_mean_nonpos
-- name    : AvramDividend.Classical.avram_p3_grid4_scaled_signed_source_mean_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:28:34.89019+00:00
-- url     : https://prove2.me/theorems/2b5f5ded-77a6-4394-a683-ddbcb5c9e908
-- title:
--   Nonnegative deterministic scaling preserves integrable signed source and its nonpositive mean
-- statement:
--   Scaling each genuine stopped compensated-jump plus HJB source by a deterministic nonnegative coefficient retains L1 and mean at most zero. No separate integrability of its martingale and drift components is imposed.

import Mathlib
open Filter MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_scaled_signed_source_mean_nonpos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hZ : ∀ n, Integrable (Z n) P ∧
      (∫ ω, Z n ω ∂P) ≤ 0) :
    ∀ n, Integrable (fun ω => a n * Z n ω) P ∧
      (∫ ω, a n * Z n ω ∂P) ≤ 0 := by sorry
