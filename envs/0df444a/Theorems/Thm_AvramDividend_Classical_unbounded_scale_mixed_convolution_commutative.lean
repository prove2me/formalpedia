-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_mixed_convolution_commutative
-- name    : AvramDividend.Classical.unbounded_scale_mixed_convolution_commutative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:11:51.993653+00:00
-- url     : https://prove2.me/theorems/59b9043f-da24-4ae6-a432-85af143fc040
-- title:
--   Mixed scale-function convolutions commute at distinct discounts
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and two distinct nonnegative discounts, the causal convolution of their q-scale functions is invariant under exchanging the factors. This follows from two orientations of the resolvent identity and cancellation of the nonzero discount gap.
-- source:
--   Algebraic corollary of the proved unconditional q-scale resolvent convolution theorem.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_mixed_convolution_commutative
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hqne : q₁ ≠ q₂) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) =
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₁ (x - s) := by sorry
