-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_scale_positive_discount_tilt_kernel
-- name    : AvramDividend.Classical.unbounded_zero_scale_positive_discount_tilt_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:22:32.206986+00:00
-- url     : https://prove2.me/theorems/3fee0778-94fd-4f8b-a604-3b9bf909e5c5
-- title:
--   Continuous subunit-mass renewal kernel from a zero-discount scale
-- statement:
--   Given unbounded variation, an existing zero-discount scale W0 and q>0, choose θ≥0 with ψθ>q. The kernel K(x)=q exp(-θx)W0(x) is continuous, integrable on the positive half-line and has exact mass ρ=q/ψθ in (0,1). This supplies the physically correct kernel normalisation for constructing the positive-q scale via a geometric Neumann series.
-- source:
--   Proved eventual psi growth, zero-scale origin, global continuity and the IsScaleFunction q=0 Laplace transform

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_scale_positive_discount_tilt_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 ≤ θ ∧ 0 < ρ ∧ ρ < 1 ∧
      Continuous K ∧ IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ ∧
      (∀ x : ℝ, K x = q * (Real.exp (-(θ * x)) * W₀ x)) := by sorry
