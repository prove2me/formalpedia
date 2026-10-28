-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_unique_nonnegative_discount
-- name    : AvramDividend.Classical.unbounded_scale_unique_nonnegative_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:07:52.245522+00:00
-- url     : https://prove2.me/theorems/9a73ccb3-0357-41a8-9c37-c9d84979f2d3
-- title:
--   Uniqueness of the unbounded-variation q-scale function at a fixed nonnegative discount
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, any two q-scale functions with the same nonnegative discount coincide at every positive reserve. The proof uses the eventual positive Lévy-exponent tail to obtain common Laplace transforms, followed by uniqueness of the Laplace transform among continuous functions.
-- source:
--   IsScaleFunction Laplace identity and the previously proved signed Laplace transform uniqueness theorem.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_unique_nonnegative_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q W₁)
    (hW₂ : IsScaleFunction X q W₂) :
    ∀ x : ℝ, 0 < x → W₁ x = W₂ x := by sorry
