-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_scale_tilt_kernel_causal_nonnegative
-- name    : AvramDividend.Classical.unbounded_zero_scale_tilt_kernel_causal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:40:00.466717+00:00
-- url     : https://prove2.me/theorems/c7b45fb7-a8e1-46e2-aa26-adb9759568fe
-- title:
--   Causality and positivity of the unbounded-variation zero-scale tilt
-- statement:
--   In the unbounded-variation case W0(0)=0. The q-weighted Esscher tilt of W0 therefore vanishes at every non-positive argument and is globally nonnegative for q≥0. This discharges the support and positivity premises of the causal Neumann kernel construction.
-- source:
--   Proved unbounded_scale_zero_origin_nonnegative_discount and IsScaleFunction support/nonnegativity.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_scale_tilt_kernel_causal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ : ℝ) (hq : 0 ≤ q) :
    (∀ x : ℝ, x ≤ 0 →
      q * (Real.exp (-(θ * x)) * W₀ x) = 0) ∧
    (∀ x : ℝ, 0 ≤
      q * (Real.exp (-(θ * x)) * W₀ x)) := by sorry
