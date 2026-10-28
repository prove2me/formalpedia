-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
-- name    : AvramDividend.Classical.killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:58:39.31738+00:00
-- url     : https://prove2.me/theorems/34553017-089b-4bac-9ed5-29a6d6eeb7c5
-- title:
--   Every successful higher record entails survival of the earlier lower record
-- statement:
--   If a higher strict first-upcrossing occurs before reflected barrier ruin, then every preceding lower-level strict upcrossing also occurs before ruin. This supplies the event inclusion used to zero out the finite-horizon killed-next-record payoff outside the stopped-history survival event. The declaration explicitly opens MeasureTheory for Measure and Filtration.
-- source:
--   Proved twoSidedExitUpTime_mono_threshold and transitivity of the ENNReal strict order.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_higherRecord_survival_implies_lowerRecord_survival_with_measure_import
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b ε : ℝ)
    (hε : 0 ≤ ε) (ω : Ω)
    (hHigher : twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω) :
    twoSidedExitUpTime X b ω < barrierRuinTime X a ω := by sorry
