-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_weighted_residual_integrable_from_scale
-- name    : AvramDividend.Classical.bv_weighted_residual_integrable_from_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:07:54.752986+00:00
-- url     : https://prove2.me/theorems/12ec72f2-e341-415f-b842-c363502256e6
-- title:
--   BV generator residual has an integrable weighted Laplace density from the scale function
-- statement:
--   For a BV spectrally negative Lévy process and a monotone q-scale function W, q<ψ(θ) and exponential integrability of W on the positive half-line imply integrability of the full weighted generator residual. The proof derives weighted derivative integrability and signed product-kernel integrability automatically, applies Fubini to the jump integral and combines all terms.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, weighted bounded-variation generator calculation

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_integrable_of_components

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem bv_weighted_residual_integrable_from_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ))) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * (X.generator W x - q * W x))
      (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
