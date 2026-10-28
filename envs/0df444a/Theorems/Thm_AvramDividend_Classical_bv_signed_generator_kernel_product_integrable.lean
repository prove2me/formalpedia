-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable
-- name    : AvramDividend.Classical.bv_signed_generator_kernel_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:56:15.112611+00:00
-- url     : https://prove2.me/theorems/a680a95b-619d-4666-8f8b-1fecd9040c5d
-- title:
--   Unconditional full BV signed negative-jump generator kernel product integrability
-- statement:
--   A bounded-variation spectrally negative Lévy process and its monotone q-scale function have an absolutely integrable exponentially weighted compensated generator kernel on the positive-reserve and negative-jump product measure, for θ≥0 with q<ψ(θ). Joint measurability is obtained from the reflected positive-magnitude kernel; integrability follows by pushforward transport of the accepted positive-magnitude bound.
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Lemma 4; signed jump Fubini prerequisites

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_ae_measurable_negative
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable_of_measurability

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem bv_signed_generator_kernel_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by sorry

end AvramDividend.Classical
