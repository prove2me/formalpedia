-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_observation_of_strict_downcrossing
-- name    : AvramDividend.Classical.twoSidedExitDownTime_le_observation_of_strict_downcrossing
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-25T20:40:53.694857+00:00
-- url     : https://prove2.me/theorems/3523baea-9f1a-4ba9-becc-b3dcb2d9e2f7
-- title:
--   Canonical strict lower ruin clock is bounded by any observed strict downcrossing time
-- statement:
--   For any spectrally negative Lévy process and initial reserve x, the canonical strict lower exit (ruin) clock, defined as an ENNReal infimum over observations satisfying X_s < -x, is at most every observation time s where that strict downward crossing occurs. This deterministic first-passage bound is the counterpart to the strict upper-clock lemma and is useful when proving two-sided stopped-scale and ruin boundary identities.
-- source:
--   Definition of twoSidedExitDownTime as nested iInf and the order-theoretic iInf_le rule.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_le_observation_of_strict_downcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (s : ℝ≥0)
    (hs : X.X s ω < -x) :
    twoSidedExitDownTime X x ω ≤ (s : ℝ≥0∞) := by sorry
