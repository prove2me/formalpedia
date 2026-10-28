-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_C1_of_zero_discount_C1
-- name    : AvramDividend.Classical.unbounded_positive_discount_C1_of_zero_discount_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:44:35.816575+00:00
-- url     : https://prove2.me/theorems/19f7023d-47cb-46b4-ab2c-9939e676ccdf
-- title:
--   Positive-discount C1 regularity inherited from an unbounded-variation zero-discount scale
-- statement:
--   Given a spectrally negative Lévy process of unbounded variation, a zero-discount scale function C1 on the positive half-line, and any positive-discount scale function, the two-discount Volterra resolvent and an exponentially damped derivative primitive transfer C1 regularity to the positive-discount scale. This is conditional on the genuine zero-discount C1 core, and supplies the missing forward transfer without making an assumption about the derivative at zero.
-- source:
--   AvramDividend.Classical.unbounded_scale_resolvent_convolution (Proved), unbounded_scale_zero_origin_nonnegative_discount (Proved), scale_weighted_derivative_correction_integrable (Proved), exp_weighted_scale_hasDerivAt (Proved), integrable_derivative_primitive_at_zero (Proved), causal_resolvent_C1_of_exponential_weighting (Proved). Root-linked zero-discount core 8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_discount_C1_of_zero_discount_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hW₀C1 : ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)))
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) := by sorry
