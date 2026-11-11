-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys51_original_actual_negative_count_L1
-- name    : AvramDividend.Classical.avram_bvb_phys51_original_actual_negative_count_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:03:18.383927+00:00
-- url     : https://prove2.me/theorems/1d9db509-7270-49e2-9f7a-cfd393d7cc56
-- title:
--   Original finite-activity negative jump count has finite first moment on a bounded horizon
-- statement:
--   The realised number of strictly negative jumps of the original spectrally negative Lévy process in a bounded deterministic interval is integrable whenever its negative Lévy intensity is finite.
-- source:
--   Necessary count-integrability component of Open 9a6793e4 fullmask jump count majorant, used in the original physical BV source route to 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys51_original_actual_negative_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Integrable (fun ω : Ω =>
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ))).toReal) P := by sorry
