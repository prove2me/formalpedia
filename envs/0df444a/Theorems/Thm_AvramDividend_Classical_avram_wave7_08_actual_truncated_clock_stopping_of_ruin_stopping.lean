-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
-- name    : AvramDividend.Classical.avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:51:14.793094+00:00
-- url     : https://prove2.me/theorems/7bcaac6d-f352-43c2-b9fc-da6a3fd7a2af
-- title:
--   Original truncated ruin clock inherits stopping-time property from source ruin time
-- statement:
--   For the genuine source ruin time in the original filtration, if the original ruin time is a stopping time, then the finite-horizon NNReal truncation of that same clock is a stopping time. The conversion is exact, using the Proved W7-08 clock-casting lemma, and the stopped-time event is either all of Ω or the original ruin event.
-- source:
--   Independent original-process clock adapter, conditional on the remaining continuous ruin stopping-time property; consumes Proved 6b7a13a0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D)) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : WithTop ℝ≥0)) := by sorry
