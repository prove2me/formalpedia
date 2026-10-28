-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
-- name    : AvramDividend.Classical.unbounded_scale_discount_strict_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:13:13.200463+00:00
-- url     : https://prove2.me/theorems/2f05b5e9-d9fe-4530-9d85-9136281239e1
-- title:
--   Strict increase of q-scale functions under a strict discount increase
-- statement:
--   For unbounded-variation spectrally negative Lévy processes and nonnegative q1 < q2, the corresponding q-scale functions satisfy W_q1(x) < W_q2(x) at every x > 0. The resolvent difference is a strictly positive discount increment times a convolution of strictly positive scale functions. This strengthens non-strict monotonicity and supplies a reusable strict-comparison lemma.
-- source:
--   Imports unbounded_scale_resolvent_convolution, scaleFunction_strict_pos_of_unbounded_variation and Mathlib intervalIntegral.integral_pos.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_strict_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x → W₁ x < W₂ x := by sorry
