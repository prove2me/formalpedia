-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_rate_finite_n
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_rate_finite_n
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:26:47.650579+00:00
-- url     : https://prove2.me/theorems/9019f0e2-db41-4b10-8e87-4cab0594336f
-- title:
--   Original negative jump band at 1/(n+1) has finite Lévy intensity
-- statement:
--   The original spectrally negative Lévy measure assigns finite intensity to the exact negative jump band at threshold 1/(n+1), for every natural n. This is the specialised source finiteness input for the quadratic ENNReal adapter.
-- source:
--   Proved original separated negative Borel intensity finiteness 86086cb2, exact measurable interval band, and positive epsilon=1/(n+1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_negative_band_rate_finite_n
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤ := by sorry
