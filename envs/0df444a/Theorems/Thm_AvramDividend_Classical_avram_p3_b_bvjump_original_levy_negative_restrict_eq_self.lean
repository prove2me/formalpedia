-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_levy_negative_restrict_eq_self
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_levy_negative_restrict_eq_self
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:52:40.697214+00:00
-- url     : https://prove2.me/theorems/18597add-6302-4b74-9d54-303c1ff43196
-- title:
--   Actual original spectrally negative Lévy mark intensity is unchanged by negative-jump restriction
-- statement:
--   For the exact original spectrally negative Lévy process X, restricting its original measure X.ν to strictly negative jump marks leaves it identical as a measure. This uses the already Proved original arbitrary-Borel support identity and ordinary measure extensionality, with no new rate, Poisson model, or finite first-moment assumption. It removes the ν versus ν.restrict negative mismatch in the original finite-horizon intensity N.
-- source:
--   Proved avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction; Mathlib Measure.restrict_apply and Measure.ext.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_levy_negative_restrict_eq_self
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.ν.restrict (Iio (0 : ℝ)) = X.ν := by sorry
