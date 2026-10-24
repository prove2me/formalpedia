-- Prove2me | Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
-- name    : AvramDividend.Classical.survival_event_measurable_of_stopping_and_admissible
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T23:22:27.631466+00:00
-- url     : https://prove2.me/theorems/e340e4be-5f7b-44d6-b526-434e0429f761
-- title:
--   Measurability of survival before a stopping horizon for an admissible dividend strategy
-- statement:
--   Given an admissible dividend strategy, the first strict ruin time is measurable by the canonically Proved ruinTime_measurable theorem. A stopping horizon is measurable by IsStoppingTime.measurable. The inverse image of the strict order relation on extended nonnegative real times is measurable, hence the pre-ruin survival event is measurable. This supplies the explicit survival-set premise of the progressive stopped-test helper.
-- source:
--   Mathlib Probability Process Stopping IsStoppingTime.measurable and BorelSpace.Order measurableSet_lt; canonical AvramDividend.Classical.ruinTime_measurable.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.survival_event_measurable_of_stopping_and_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    MeasurableSet {ω : Ω | τ ω < ruinTime X x D ω} := by sorry
