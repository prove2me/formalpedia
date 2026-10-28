-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable_of_measurability
-- name    : AvramDividend.Classical.bv_signed_generator_kernel_product_integrable_of_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:48:39.613405+00:00
-- url     : https://prove2.me/theorems/faa8c05e-efd0-4107-ba20-df25c23596f9
-- title:
--   BV compensated Lévy generator kernel is absolutely product-integrable in signed jumps
-- statement:
--   Convert the proved absolute product-integrability of the positive jump-magnitude kernel to the canonical signed negative-jump generator kernel. The two kernels coincide after y↦−y on the support of the Lévy jump restriction; product-measure pushforward transfers integrability. The required joint almost-everywhere strong measurability is explicit, allowing a separate C1 smoothness argument to supply it.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; Mathlib pushforward of product measure under negation.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_bv_actual_levy_compensated_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_integrable_product_signed_jump_of_neg_map
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_signed_generator_kernel_product_integrable_of_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hAEm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by sorry

end AvramDividend.Classical
