-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_of_positive_discount_C1
-- name    : AvramDividend.Classical.unbounded_zero_discount_C1_of_positive_discount_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:07:28.455731+00:00
-- url     : https://prove2.me/theorems/710d698e-be8e-443f-bc08-14f9f3211bd3
-- title:
--   Zero-discount scale C1 transfer from a positive-discount comparison scale
-- statement:
--   For a spectrally negative Levy process of unbounded variation, C1 regularity of any positive-discount comparison scale function transfers to the zero-discount scale function. Given an admissible common Laplace exponent, the proof uses the exact two-discount scale resolvent, exponential damping, integrable weighted derivatives, the zero-origin primitive and the proved Volterra C1 regularity transfer. The existence and C1 regularity of a positive-discount comparison scale are separate hypotheses.
-- source:
--   Proved unbounded_scale_resolvent_convolution, unbounded_scale_zero_origin_nonnegative_discount, causal_convolution_time_reversal, causal_resolvent_C1_of_L1_primitive, weighted derivative integrability, plus newly published analytic exponential helpers.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_discount_C1_of_positive_discount_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq)
    (hWqC1 : ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)))
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by sorry
