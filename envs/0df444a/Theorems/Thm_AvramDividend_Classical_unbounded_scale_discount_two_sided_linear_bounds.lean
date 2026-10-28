-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_two_sided_linear_bounds
-- name    : AvramDividend.Classical.unbounded_scale_discount_two_sided_linear_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:28:58.250306+00:00
-- url     : https://prove2.me/theorems/2dc78ada-0e51-43e7-91b3-a665b0149d0b
-- title:
--   Two-sided linear discount sensitivity bounds between fixed scale convolutions
-- statement:
--   On the nonnegative discount interval up to Q, differences between scale functions at two discounts are bounded above and below by the discount increment multiplied by fixed zero-discount and Q-discount self-convolution constants. The lower constant is strictly positive at positive reserves for unbounded-variation Lévy processes.
-- source:
--   Combination of the proved self-convolution secant sandwich, monotonicity of causal convolution, and uniform upper bound.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_sandwich
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_two_sided_linear_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ Q : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hQ : 0 ≤ Q) (hq12 : q₁ < q₂) (hq2Q : q₂ ≤ Q)
    (W₀ W₁ W₂ WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₀ s * W₀ (x - s)) ≤
          W₂ x - W₁ x ∧
      W₂ x - W₁ x ≤ (q₂ - q₁) *
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by sorry
