-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_zero_discount
-- name    : AvramDividend.Classical.unbounded_scale_zero_origin_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:54:08.550079+00:00
-- url     : https://prove2.me/theorems/7b9f311a-83e2-4d3f-a798-5574e6897974
-- title:
--   Every unbounded-variation zero-discount q-scale function vanishes at zero
-- statement:
--   Direct, non-circular necessary boundary condition for root-connected unbounded_scale_C1_zero_discount_core (8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d), which is the sole missing case of scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q. Under ¬BoundedVariation, either σ>0, or σ=0 with an infinite small-negative-jump first moment. In each case a proven superlinear ψ/θ growth theorem applies. The now-Proved scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q yields W(0)=0 at q=0. This closes the origin-boundary prerequisite without presupposing positive q, and reduces the remaining C1 challenge to differentiability on the strictly positive half-line.
-- source:
--   Definitions.BoundedVariation; Proved psi_normalised_unbounded_small_jumps (3fc04011-a4da-4c0d-a8b8-9ac3ecf6a855); newly Proved scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q (097a29e5-ff86-4f5d-b65b-f952540cc19d); Gaussian superlinear growth helper c1392cb2-b5da-4f7e-b8e7-854fe3d2ee4f.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_zero_origin_zero_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hW : IsScaleFunction X 0 W)
    (hnbv : ¬ X.BoundedVariation) :
    W 0 = 0 := by sorry
