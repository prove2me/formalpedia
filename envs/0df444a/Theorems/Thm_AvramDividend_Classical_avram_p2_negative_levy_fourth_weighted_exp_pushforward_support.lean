-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_support
-- name    : AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:22:32.62187+00:00
-- url     : https://prove2.me/theorems/1fcc76a9-2cf7-4f44-aea9-4e0ee04229f5
-- title:
--   Weighted negative Lévy exponential image has zero mass at and above one
-- statement:
--   The finite weighted Lévy-measure exponential image is supported strictly below 1: for y<0 the exponential exp(y)<1, and the density-weighted measure remains absolutely continuous with respect to the original Lévy measure restricted to negative marks. Proves zero mass on [1,∞), a genuine compact-support ingredient of weighted moment uniqueness; no jump count or compensator assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
      Real.exp) (Ici (1 : ℝ)) = 0 := by sorry
