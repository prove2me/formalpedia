-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_success_antitone_upper_barrier
-- name    : AvramDividend.Classical.chat04_strict_exit_success_antitone_upper_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:26:46.142678+00:00
-- url     : https://prove2.me/theorems/86766f81-94ec-4731-a975-cb9d15b65dfa
-- title:
--   Raising a strict upper exit barrier delays passage and shrinks the success event
-- statement:
--   For fixed initial reserve x and lower ruin boundary -x, increasing the upper level from a to b with a≤b delays the strict upward first-passage time, including infinite values. Any sample path that crosses the higher level before ruin also crosses the lower level before ruin. The conclusion is pointwise and preserves the exact strict stopping conventions.
-- source:
--   Direct order comparison for the sInf definitions of the strict two-sided exit clocks from Avram et al. (2007), equation (3.6).

import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_success_antitone_upper_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x : ℝ) (hab : a ≤ b) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω ≤
      twoSidedExitUpTime X (b - x) ω ∧
    (twoSidedExitUpTime X (b - x) ω <
       twoSidedExitDownTime X (-x) ω →
     twoSidedExitUpTime X (a - x) ω <
       twoSidedExitDownTime X (-x) ω) := by sorry
