-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:24:30.939498+00:00
-- url     : https://prove2.me/theorems/c33d51be-e7d9-4f92-8522-9e06af631388
-- title:
--   Original finite-activity negative Lévy small-strip first-moment upper bound
-- statement:
--   For the original spectrally negative Lévy process with finite negative jump intensity, the nonnegative first-moment integral on (-epsilon,0) is at most epsilon times the total negative-jump intensity. This controls the deterministic compensated strip remaining after the original physical jump marks vanish.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∫⁻ z in Ioo (-ε) 0, ENNReal.ofReal |z| ∂X.ν) ≤
      ENNReal.ofReal ε * X.ν (Iio (0 : ℝ)) := by sorry
