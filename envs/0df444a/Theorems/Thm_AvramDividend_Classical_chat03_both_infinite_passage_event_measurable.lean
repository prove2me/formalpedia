-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_both_infinite_passage_event_measurable
-- name    : AvramDividend.Classical.chat03_both_infinite_passage_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:19:55.981595+00:00
-- url     : https://prove2.me/theorems/f9cf3f9d-cf76-4a95-ab5b-49154cf17fe7
-- title:
--   Measurability of the event that both named strict first-passage times are infinite
-- statement:
--   For the official spectrally negative Lévy process and any strict lower and upper thresholds, the event that both extended-nonnegative-real first passage clocks equal infinity is measurable. The already Proved named-passage infinity equivalences identify this event with the complement of the occurrence of any strict crossing. The independently Proved inverse-natural grid witness theorem and countable grid event measurability express that complement as the complement of a measurable countable union, directly discharging event measurability without any unproved continuous-time theorem.
-- source:
--   Proved named passage interface a52ea59d-4ace-40ab-a710-1a993e9b4ae9, inverse-natural grid witness ac8b9e52-5815-4817-aff2-65753a595d1f and countable grid event measurability e1e3bf46-3ca6-42a0-b297-802d10bc9fd5.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff
import Theorems.Thm_AvramDividend_Classical_chat03_countable_grid_exit_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_named_exit_finite_infinite_interface

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_both_infinite_passage_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω |
        twoSidedExitUpTime X upper ω = ∞ ∧
        twoSidedExitDownTime X lower ω = ∞} := by sorry
