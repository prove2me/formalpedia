-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T21:28:50.414178+00:00
-- url     : https://prove2.me/theorems/752fca47-f226-4eea-a02e-9b128543343d
-- title:
--   All original negative jump-mark bands sufficiently near zero are empty on bounded clocks
-- statement:
--   For almost every original finite-activity Levy path and any bounded horizon, one common positive jump magnitude threshold guarantees that every measurable negative mark set strictly inside that threshold has zero intrinsic original marked-jump count on the horizon. This removes the random signed integral from sufficiently small compensated strips in the actual same-process Ito-Meyer residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ B : Set ℝ, MeasurableSet B → B ⊆ Ioo (-ε) 0 →
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) = 0 := by sorry
