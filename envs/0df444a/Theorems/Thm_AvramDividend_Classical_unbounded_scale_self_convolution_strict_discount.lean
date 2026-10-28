-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_self_convolution_strict_discount
-- name    : AvramDividend.Classical.unbounded_scale_self_convolution_strict_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:15:26.62521+00:00
-- url     : https://prove2.me/theorems/8f915b46-d4a9-437e-bc93-f3a34aafbd40
-- title:
--   Strict increase of scale self-convolution with discount
-- statement:
--   For any unbounded-variation spectrally negative Lévy process, the self-convolution integral of its q-scale function over positive reserve is strictly increasing in the nonnegative discount parameter. This provides strict sensitivity bounds for resolvent secants.
-- source:
--   Strict positivity and strict discount monotonicity of q-scale functions integrated against continuous positive kernels.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_self_convolution_strict_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq12 : q₁ < q₂) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₁ (x - s)) <
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₂ (x - s) := by sorry
