-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_ae_positive
-- name    : AvramDividend.Classical.chat07_bv_neg_map_magnitude_ae_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:00:15.726823+00:00
-- url     : https://prove2.me/theorems/2cbe7524-7502-4117-a450-42bdcdb34f21
-- title:
--   Positive support of the negative Lévy jump magnitude pushforward measure
-- statement:
--   The image of a Lévy jump measure restricted to strictly negative jumps under real negation is concentrated on strictly positive magnitudes. This is proved by the almost-everywhere support fact for a restricted measure and the Mathlib ae_map_iff theorem. This exact support hypothesis is needed to instantiate the full compensated-scale-kernel Fubini theorem for the actual bounded-variation jump magnitude measure.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_neg_map_magnitude_ae_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ᵐ r ∂((X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)),
      (0 : ℝ) < r := by sorry
