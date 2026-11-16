-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_marked_large_only_count_small_band_zero
-- name    : AvramDividend.Classical.avram_b27_marked_large_only_count_small_band_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:22:13.02765+00:00
-- url     : https://prove2.me/theorems/fa72232c-933e-4dc4-a1e4-d8a1f77ef237
-- title:
--   Original marked-jump pushforward has zero small-negative-band integral when every mark is zero or at most minus one
-- statement:
--   For a measure μ on time and an almost-everywhere measurable marked-jump map f taking values in time×mark, if every mark is zero or at most -1 then its pushforward μ.map f assigns zero mass to the exact original small band (0,t]×(-1,-1/(n+1)], so the signed marked-count integral over that band is identically zero. Apply μ=Measure.count.restrict(original nonzero jumps) and f=(time, original X jump mark) to the B25 Brownian minus 2N example. The required AEMeasurable f remains an explicit separate stochastic-source obligation.
-- source:
--   Exact Prove2Me original intrinsic marked-jump source from avram_p4_h_gaussian_intrinsic_small_band_compensated (66a113ed), 15 November 2026.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_b27_marked_large_only_count_small_band_zero
    (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ≥0 × ℝ)
    (hf : AEMeasurable f μ)
    (hLarge : ∀ u : ℝ≥0, (f u).2 = 0 ∨ (f u).2 ≤ -1)
    (n : ℕ) (t : ℝ≥0) :
    (∫ p in (Ioc (0 : ℝ≥0) t ×ˢ
        Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))),
      p.2 ∂(μ.map f)) = 0 := by sorry
