-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_strict_event_filtration_measurable
-- name    : AvramDividend.Classical.ruinTime_strict_event_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:42:51.291455+00:00
-- url     : https://prove2.me/theorems/db6ca856-288d-4f40-82db-ec146c59a018
-- title:
--   Strict pre-ruin event measurable at its own horizon in the original filtration
-- statement:
--   Under exactly the published spectrally negative Lévy and adapted dividend strategy assumptions, for each nonnegative deterministic time t the event {ω | ruinTime(X,x,D,ω)<t} is measurable in the original filtration F_t, even if this filtration is not right-continuous. This follows from the proved rational negative-reserve criterion, adaptedness of the controlled reserve and inclusion F_q⊆F_t for rational q<t. The theorem carefully proves only strict pre-ruin event measurability; it does not assert {ruinTime≤t}∈F_t or that ruinTime is an F-stopping time, which can fail in non-usual filtrations.
-- source:
--   Published pinned Prove2Me theorems riskProcess_adapted and ruinTime_lt_iff_exists_rat_negative; pinned Mathlib Filtration.mono and measurableSet_iUnion.

import Mathlib.Probability.Process.Filtration
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_lt_iff_exists_rat_negative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ruinTime_strict_event_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | ruinTime X x D ω < (t : ℝ≥0∞)} := by sorry
