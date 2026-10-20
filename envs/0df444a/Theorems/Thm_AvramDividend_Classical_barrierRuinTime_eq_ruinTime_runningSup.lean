-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
-- name    : AvramDividend.Classical.barrierRuinTime_eq_ruinTime_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:03:32.646473+00:00
-- url     : https://prove2.me/theorems/739bd703-79ac-4350-80c8-6b15bf01b836
-- title:
--   Actual reflected-drawdown ruin time equals controlled ruin time using the true running-supremum dividends
-- statement:
--   The original strict drawdown-barrier ruin horizon of a spectrally negative Lévy process coincides pathwise with its original controlled-reserve ruin horizon when starting capital is the barrier and cumulative dividends are the genuine running supremum of the Lévy process. At each nonnegative time the controlled reserve is a + X_t - runningSup_t, so it is negative exactly when the actual reflected drawdown runningSup_t-X_t exceeds a. The equality holds for the infima in extended nonnegative time, including unattained infinities and equality at the boundary. This converts original stopped-barrier payouts to the previously proved general controlled-ruin-measurability framework.
-- source:
--   Original published definitions ruinTime, riskProcess, barrierRuinTime, drawdown, reflectedSup; proved barrierValue_self_eq_barrierSupValue target 11b589b7-37f0-4756-acd5-e1ea2d41f67a, whose accepted source simplifies this exact stopping-time relation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierRuinTime_eq_ruinTime_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    barrierRuinTime X a = ruinTime X a (runningSup X) := by sorry
