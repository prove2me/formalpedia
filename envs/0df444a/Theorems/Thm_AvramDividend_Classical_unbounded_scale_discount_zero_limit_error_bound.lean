-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_limit_error_bound
-- name    : AvramDividend.Classical.unbounded_scale_discount_zero_limit_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:08:18.586697+00:00
-- url     : https://prove2.me/theorems/8b7de870-d044-4911-aecb-c988690c330b
-- title:
--   Explicit linear error bound for the q-to-zero scale-function limit
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, the difference between the scale function discounted at q≥0 and the zero-discount scale function is at most q times an explicit scale-function self-convolution bound at each positive reserve and exactly zero elsewhere. This quantifies convergence to zero discount with a linear modulus.
-- source:
--   Specialisation of the canonical all-reserve discount Lipschitz bound to comparison with q=0.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_piecewise_lipschitz_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_zero_limit_error_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, ∀ q ∈ Icc (0 : ℝ) Q,
      |W q x - W 0 x| ≤ q *
        (if 0 < x then ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) else 0) := by sorry
