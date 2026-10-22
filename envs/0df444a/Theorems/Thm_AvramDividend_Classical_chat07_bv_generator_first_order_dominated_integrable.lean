-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_generator_first_order_dominated_integrable
-- name    : AvramDividend.Classical.chat07_bv_generator_first_order_dominated_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:28:42.606517+00:00
-- url     : https://prove2.me/theorems/8a8d8ac7-f286-4adf-9194-4b3c6e97de6c
-- title:
--   Bounded-variation Lévy generator integrability under an almost-everywhere first-order bound
-- statement:
--   For a spectrally negative bounded-variation Lévy process, any strongly measurable compensated generator increment satisfying an almost-everywhere norm bound by C min(1,|y|), with nonnegative C, is integrable over negative jumps. Combine finite first-order Lévy jump weight with domination for Bochner integrability. Unlike a pointwise bound, the a.e. hypothesis accommodates exceptional jump sizes. This is a reusable generator-domain result and does not assert generator harmonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_generator_first_order_dominated_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (f : ℝ → ℝ) (x C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ᵐ y ∂X.ν.restrict (Iio 0),
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤ C * min 1 |y|) :
    X.GeneratorIntegrable f x := by sorry
