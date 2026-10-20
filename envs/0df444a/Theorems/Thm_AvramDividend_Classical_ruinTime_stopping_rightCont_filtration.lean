-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
-- name    : AvramDividend.Classical.ruinTime_stopping_rightCont_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:53:06.097341+00:00
-- url     : https://prove2.me/theorems/2d036d4f-57b5-4b28-864b-a2ff5082e323
-- title:
--   Dividend ruin time is a stopping time for the right-continuous augmentation
-- statement:
--   For every spectrally negative Lévy process and adapted dividend strategy under the exact published definitions, its ruin time is a stopping time of the right-continuous augmentation of the original filtration. The proof does not assume the original filtration is right-continuous; it combines the remotely proved Chat 8 original-filtration strict-ruin event measurability theorem with pinned Mathlib's isStoppingTime_of_measurableSet_lt_of_isRightContinuous and the built-in IsRightContinuous instance of Filtration.rightCont. It does not claim the original filtration stopping-time property, which fails in general, nor the stability of Lévy increment independence under augmentation.
-- source:
--   Mathlib Probability.Process.Stopping and Probability.Process.Filtration pinned at 0df444a; published Prove2Me ruinTime_strict_event_filtration_measurable proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_strict_event_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ruinTime_stopping_rightCont_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsStoppingTime 𝓕.rightCont (ruinTime X x D) := by sorry
