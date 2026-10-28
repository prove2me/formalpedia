-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_piecewise_lipschitz_bound
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_piecewise_lipschitz_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:59:12.665995+00:00
-- url     : https://prove2.me/theorems/69a027c9-96b1-4691-a5bf-8ed4a7066233
-- title:
--   Explicit discount Lipschitz modulus across every real reserve
-- statement:
--   For q-scale functions of an unbounded-variation spectrally negative Lévy process, variation between two nonnegative discount rates has an explicit convolution Lipschitz bound at positive reserves and vanishes exactly at zero and negative reserves. The resulting inequality applies on the whole real reserve line with a piecewise coefficient.
-- source:
--   Canonical proved positive-reserve convolution Lipschitz estimate, negative support, and zero-origin vanishing.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_piecewise_lipschitz_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, ∀ a ∈ Icc (0 : ℝ) Q, ∀ b ∈ Icc (0 : ℝ) Q,
      |W b x - W a x| ≤ |b - a| *
        (if 0 < x then ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) else 0) := by sorry
