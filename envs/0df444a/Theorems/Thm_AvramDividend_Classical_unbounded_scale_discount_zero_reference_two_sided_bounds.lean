-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_reference_two_sided_bounds
-- name    : AvramDividend.Classical.unbounded_scale_discount_zero_reference_two_sided_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:08:00.602291+00:00
-- url     : https://prove2.me/theorems/9046bec0-a7c9-411f-a804-68c2eb4cf844
-- title:
--   Two-sided quantitative bounds for positive-discount scale deviations from zero discount
-- statement:
--   For unbounded variation, the variation in scale function from undiscounted q=0 to any positive discount q≤Q is bounded below by q times self-convolution of W0 and above by q times self-convolution of WQ, pointwise on every positive reserve.
-- source:
--   The already-Proved general two-sided discount secant estimate, specialised to a zero lower discount endpoint.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_two_sided_linear_bounds
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_zero_reference_two_sided_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q Q : ℝ) (hq : 0 < q) (hqQ : q ≤ Q)
    (W₀ Wq WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hWq : IsScaleFunction X q Wq)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      q * (∫ s in Ioc (0 : ℝ) x, W₀ s * W₀ (x - s)) ≤
        Wq x - W₀ x ∧
      Wq x - W₀ x ≤ q *
        (∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s)) := by sorry
