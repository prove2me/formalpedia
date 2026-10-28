-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_injective
-- name    : AvramDividend.Classical.unbounded_scale_discount_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:36:54.477988+00:00
-- url     : https://prove2.me/theorems/a7678cf1-6c96-401b-b18b-71f082a8d885
-- title:
--   A positive-reserve scale-function value identifies its discount rate
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, the map from any nonnegative discount rate q to the corresponding q-scale function evaluated at one fixed positive reserve is injective. Equality of scale values forces equality of discounts.
-- source:
--   Order-theoretic consequence of the Proved strict increase of scale functions with nonnegative discount.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_injective
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂)
    (x : ℝ) (hx : 0 < x) (heqW : W₁ x = W₂ x) :
    q₁ = q₂ := by sorry
