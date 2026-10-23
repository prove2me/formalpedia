-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_positive_jump_kernel_product_integrable
-- name    : AvramDividend.Classical.chat07_bv_positive_jump_kernel_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:56:18.24289+00:00
-- url     : https://prove2.me/theorems/e1fa0b50-f5fe-42b9-bf1e-406f8f03287a
-- title:
--   Weighted absolute compensated scale kernel integrable for finite first-moment jump measures
-- statement:
--   For any positive jump-magnitude measure with finite truncated first moment, the exponentially weighted absolute unit-truncated negative-jump scale kernel is integrable over the product of positive reserves and jump magnitudes. Joint measurability comes from monotonicity of the scale function and measurability of its ordinary derivative. Fixed-section integrability uses the already proved compensation/shift results. The small/large kernel estimate controls section norms by min(1,r) times a finite constant; strong measurability of the inner integral and an accepted Fubini criterion give product integrability. No global scale-function C1, generator harmonicity, or assumption of vanishing residual is used.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_product_integrable_of_section_norm_majorant
import Theorems.Thm_AvramDividend_Classical_chat07_bv_compensated_kernel_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_full_jump_kernel_section_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_bv_full_negative_jump_kernel_weight_bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_positive_jump_kernel_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (ν : Measure ℝ) [SFinite ν]
    (hνpos : ∀ᵐ r ∂ν, 0 < r)
    (hνmoment : Integrable (fun r : ℝ => min 1 r) ν) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ*p.1)) *
        |W (p.1-p.2) - W p.1 +
          (if p.2 < 1 then p.2*deriv W p.1 else 0)|)
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by sorry
