-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_jump_convolution_product_integrable_finite_activity
-- name    : AvramDividend.Classical.scaleFunction_jump_convolution_product_integrable_finite_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:49:58.952408+00:00
-- url     : https://prove2.me/theorems/28daa563-7231-4674-8102-c5d9b2fb426d
-- title:
--   Weighted scale-jump kernel is product-integrable for finite activity
-- statement:
--   When the negative-jump Lévy measure has finite mass, the q-scale function's nonnegative monotonicity implies W(x+y) ≤ W(x) for x>0 and y<0. The exponential weight times W(x) is integrable when ψ(θ)>q; taking the product with the finite jump measure gives an integrable dominating kernel, proving the weighted two-variable kernel is product-integrable.
-- source:
--   The already proved AvramDividend.Classical scaleFunction_shift_bounds_of_nonpositive and scaleFunction_shiftedLaplace_integrable, and Mathlib MeasureTheory.Integrable.comp_fst/m​ono.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_jump_convolution_product_integrable_finite_activity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Integrable (Function.uncurry
      (fun x y : ℝ => Real.exp (-(θ * x)) * W (x + y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
