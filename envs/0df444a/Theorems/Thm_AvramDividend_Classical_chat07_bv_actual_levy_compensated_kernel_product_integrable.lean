-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_actual_levy_compensated_kernel_product_integrable
-- name    : AvramDividend.Classical.chat07_bv_actual_levy_compensated_kernel_product_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T08:22:42.018169+00:00
-- url     : https://prove2.me/theorems/80d81e4f-3691-4234-a406-68ff4ec130e1
-- title:
--   Full BV negative Lévy generator jump kernel is absolutely product-integrable
-- statement:
--   For a bounded-variation spectrally negative Lévy process, under the standard scale-function and admissible positive Laplace parameter assumptions, the exponentially weighted absolute compensated jump kernel is integrable jointly over positive reserves and the actual negative-jump magnitude measure, obtained by restricting the Lévy measure to negative jumps and applying negation. The theorem combines the proved abstract positive jump magnitude product-integrability result with the separately proved finite truncated first moment and positive support of this exact pushforward measure. It closes the essential Fubini/Tonelli absolute-integrability prerequisite for the BV generator scale-function harmonicity programme without assuming that harmonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_bv_positive_jump_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_ae_positive
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_actual_levy_compensated_kernel_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ*p.1)) *
        |W (p.1-p.2) - W p.1 +
          (if p.2 < 1 then p.2*deriv W p.1 else 0)|)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        ((X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y))) := by sorry
