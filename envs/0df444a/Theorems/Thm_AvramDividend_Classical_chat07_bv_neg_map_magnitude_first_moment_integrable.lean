-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_neg_map_magnitude_first_moment_integrable
-- name    : AvramDividend.Classical.chat07_bv_neg_map_magnitude_first_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:59:10.066569+00:00
-- url     : https://prove2.me/theorems/d24909b1-d812-4e65-839e-8c0ab956e8c7
-- title:
--   Finite BV truncated first moment of the negative Lévy pushforward magnitude measure
-- statement:
--   Let ν be a bounded-variation spectrally negative Lévy process's jump measure, restricted to strictly negative jumps and pushed forward along y↦-y. Its positive-magnitude image has finite first truncated moment ∫min(1,r). This is the precise pushforward-measure hypothesis needed for the already developed product-integrability theorem, proved from the accepted negative-jump first-moment integrability and Mathlib's integrability-under-measure-map criterion.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_neg_map_magnitude_first_moment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    Integrable (fun r : ℝ => min (1 : ℝ) r)
      ((X.ν.restrict (Iio (0 : ℝ))).map (fun y : ℝ => -y)) := by sorry
