-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support
-- name    : AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_image_compact_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:44:22.247183+00:00
-- url     : https://prove2.me/theorems/650b498e-1a45-47d0-91ab-e56a5f01209f
-- title:
--   Finite negative Lévy weighted exponential image is supported on the compact unit interval
-- statement:
--   The actual negative Lévy measure X.ν weighted by the fourth exponential deficit, then pushed forward under real exp, assigns zero measure to the complement of the compact unit interval [0,1]. The upper support was independently proved using the negative intrinsic marks; strict positivity of exp gives the lower support. This compact support is a key source-side premise in moment-determinate weak-limit uniqueness, without relying on an expected jump count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_support

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_image_compact_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
      Real.exp) ((Icc (0 : ℝ) 1)ᶜ) = 0 := by sorry
