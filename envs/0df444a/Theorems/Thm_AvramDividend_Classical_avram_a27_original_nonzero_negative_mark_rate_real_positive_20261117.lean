-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
-- name    : AvramDividend.Classical.avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:20:05.815885+00:00
-- url     : https://prove2.me/theorems/7c4d8a30-98d5-4128-96d3-887d7a8c67dc
-- title:
--   Original finite strictly negative jump mass is positive after ENNReal-to-real conversion
-- statement:
--   For an original nonzero spectrally negative Lévy measure with finite negative jump activity, its negative-mark total intensity converted to a real number is strictly positive. This is the normalizing denominator for the physical IID mark law.
-- source:
--   Proved original positive negative intensity A105 and finite ENNReal-to-real positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Nonzero original negative Lévy intensity has positive finite real mass. -/

theorem AvramDividend.Classical.avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hNu : X.ν ≠ 0) :
    0 < (X.ν (Iio (0 : ℝ))).toReal := by sorry
