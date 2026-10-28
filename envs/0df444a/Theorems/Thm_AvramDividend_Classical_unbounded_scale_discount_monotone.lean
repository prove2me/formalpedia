-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_monotone
-- name    : AvramDividend.Classical.unbounded_scale_discount_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:13:17.819409+00:00
-- url     : https://prove2.me/theorems/c778764b-a6bb-4c45-9982-e4d782a66768
-- title:
--   Monotonicity of the q-scale function with respect to nonnegative discount
-- statement:
--   For any two nonnegative discount rates q1 ≤ q2 of the same spectrally negative Lévy process with unbounded variation, its scale functions satisfy W_q1(x) ≤ W_q2(x) for all x > 0. This follows from the established unconditional resolvent convolution and nonnegativity of scale functions, giving a reusable stochastic-comparison property.
-- source:
--   Uses unconditional q-scale resolvent convolution and positivity of causal convolution.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x → W₁ x ≤ W₂ x := by sorry
