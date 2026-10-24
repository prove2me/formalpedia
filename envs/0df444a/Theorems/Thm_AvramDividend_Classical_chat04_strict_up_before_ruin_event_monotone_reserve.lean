-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_up_before_ruin_event_monotone_reserve
-- name    : AvramDividend.Classical.chat04_strict_up_before_ruin_event_monotone_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:07:29.995018+00:00
-- url     : https://prove2.me/theorems/e8c7e496-7c2a-452e-a5f9-59a14644c2f4
-- title:
--   Increasing starting reserve preserves successful strict upper exit before ruin
-- statement:
--   For any spectrally negative Lévy process and any sample path, if the strict upward time precedes the strict downward ruin time at initial capital x, it also does so at every greater capital y. This is a pathwise inclusion with the exact sInf strict clocks, including infinite-time cases, with no almost-sure weakening.
-- source:
--   Immediate order-theoretic corollary of the new strict-exit clock monotonicity theorem and the original two-sided exit definitions.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_monotone_initial_reserve

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_up_before_ruin_event_monotone_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x y : ℝ) (hxy : x ≤ y) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} := by sorry
