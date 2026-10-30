-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_uniform_nonnegative_bounded_integral_transfer
-- name    : AvramDividend.Classical.avram_ws01b_uniform_nonnegative_bounded_integral_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T14:13:56.961735+00:00
-- url     : https://prove2.me/theorems/565d6de7-91c8-469e-97ba-4ca89e359214
-- title:
--   Uniformly bounded original killed reward integral convergence
-- statement:
--   For any probability measure, nonnegative source rewards integrable and uniformly bounded by a finite real cap converge in real expectation to their almost-everywhere pointwise limit; no separate measurability assumption on the limit.
-- source:
--   Accepted generic nonnegative truncated dominated convergence, with a bound inherited by the pointwise limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_tendsto

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_uniform_nonnegative_bounded_integral_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hInt : ∀ n, Integrable (Y n) P)
    (h0 : ∀ n ω, 0 ≤ Y n ω)
    (hCap : ∀ n ω, Y n ω ≤ R)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Tendsto (fun n => ∫ ω, Y n ω ∂P)
      atTop (𝓝 (∫ ω, Z ω ∂P)) := by sorry
