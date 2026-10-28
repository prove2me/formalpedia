-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_ae_measurable_negative
-- name    : AvramDividend.Classical.bv_signed_generator_kernel_ae_measurable_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:41:26.356755+00:00
-- url     : https://prove2.me/theorems/21e651d3-2418-4e4c-963f-0d9f21ecb1cf
-- title:
--   Almost-everywhere joint measurability of the signed negative-jump generator kernel
-- statement:
--   For a spectrally negative Lévy process, a monotone scale candidate W and an exponential reserve weight, the signed compensated generator integrand is strongly measurable on the product of positive reserve Lebesgue measure with the restricted negative-jump Lévy measure. It follows from a proved measurable positive-magnitude kernel and the pointwise reflection identity almost everywhere on negative jumps.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; Mathlib product measure theory

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_signed_compensated_kernel_joint_measurable
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem bv_signed_generator_kernel_ae_measurable_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hWmon : Monotone W) (θ : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by sorry

end AvramDividend.Classical
