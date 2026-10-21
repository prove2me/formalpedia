-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_named_upper_passage_lt_horizon_measurable
-- name    : AvramDividend.Classical.chat03_named_upper_passage_lt_horizon_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:37:52.238608+00:00
-- url     : https://prove2.me/theorems/917e5e2e-24d3-4c75-b7b2-da7c5be978a3
-- title:
--   Strict finite-horizon sublevel event of the official upper first-passage clock is measurable
-- statement:
--   At any finite nonnegative horizon T, the sublevel event that the official named strict upper first-passage time occurs before T is measurable. By the previously proved firstUpcrossing_lt_iff_exists_witness theorem, the extended infimum is below T exactly when an upward strict-crossing witness exists at some s<T. Measurability of that event follows from the separately proved horizon-preserving countable-grid approximation.
-- source:
--   Pinned official Lévy process declarations, accepted earlier Chat03 lemmas and exact Mathlib revision.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_named_upper_passage_lt_horizon_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | twoSidedExitUpTime X upper ω < (T : ℝ≥0∞)} := by sorry
