-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:34:11.591908+00:00
-- url     : https://prove2.me/theorems/d34f39c4-4bd1-4798-a7d6-18501ea8a3f6
-- title:
--   Original small-jump short strip: bounded random predictor weight expectation bound
-- statement:
--   For the actual source intrinsic marked jump count on (s,r]×B and any random nonnegative weight H bounded pointwise by K, the event-restricted weighted expectation is at most K(r−s)ν(B). Uses the original count measurability and only an explicitly supplied unconditional source rate, so applies even when H is adapted/random, without an independent Poisson surrogate or deterministic-integrand substitution.
-- source:
--   Actual source negative jump count and accepted marked rectangle measurability 1f8f25b0; Mathlib lintegral_mono, lintegral_const_mul, lintegral_mono_set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_marked_bounded_random_weight_short_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Ω) (H : Ω → ℝ≥0∞) (K : ℝ≥0∞)
    (hBound : ∀ ω, H ω ≤ K)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s r ×ˢ B) ∂P) =
       ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A, H ω * ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s r ×ˢ B) ∂P) ≤
      K * (((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
