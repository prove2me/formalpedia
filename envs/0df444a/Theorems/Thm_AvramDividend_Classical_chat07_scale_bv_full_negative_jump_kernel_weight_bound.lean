-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_bv_full_negative_jump_kernel_weight_bound
-- name    : AvramDividend.Classical.chat07_scale_bv_full_negative_jump_kernel_weight_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:19:38.252174+00:00
-- url     : https://prove2.me/theorems/8fe6f643-891e-4991-855b-2ba2ba2db1b9
-- title:
--   BV negative-jump kernel weighted bound by truncated jump magnitude
-- statement:
--   For the complete negative-jump generator kernel with the standard unit truncation, the weighted absolute positive-reserve integral is bounded by min(1,r) times a finite coefficient. On jumps smaller than one this uses first-order compensated scale and weighted derivative estimates; larger jumps have no compensation and use the uniform scale displacement estimate. This casewise estimate supplies the pointwise-in-jump first-moment majorant for the bounded-variation Fubini argument.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_bv_full_negative_jump_kernel_weight_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ*x)) *
        |W (x-r) - W x + (if r < 1 then r*deriv W x else 0)|) ≤
      min 1 r * max
        (θ * (X.ψ θ - q)⁻¹ +
          (∫ x in Ioi (0 : ℝ),
             Real.exp (-(θ*x)) * deriv W x))
        ((X.ψ θ - q)⁻¹) := by sorry
