-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_compensated_lintegral_exceeds
-- name    : AvramDividend.Classical.negative_compensated_lintegral_exceeds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:27:59.037792+00:00
-- url     : https://prove2.me/theorems/29f29e99-00e2-411b-9a92-14eab62c8cbd
-- title:
--   Divergent negative-jump moment forces uniformly large normalised Laplace integral
-- statement:
--   For any real-jump measure supported almost everywhere on negative jumps whose extended absolute first moment is infinite, the normalised compensated exponential jump integral at integer Laplace parameters n+1 eventually exceeds any prescribed finite ENNReal threshold. The conclusion is uniform for all n beyond a suitable N, rather than asserting a subsequence only.
-- source:
--   Direct consequence of Prove2Me negative_compensated_lintegral_tendsto using its infinite-moment target and the order-topology neighbourhood of top. Supports the infinite-variation branch of the non-Gaussian Lévy exponent growth argument.

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_compensated_lintegral_exceeds
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν) = ⊤)
    (B : ℝ≥0∞) (hB : B < ⊤) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      B < (∫⁻ y : ℝ,
        ENNReal.ofReal
          ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ∂ν) := by sorry
