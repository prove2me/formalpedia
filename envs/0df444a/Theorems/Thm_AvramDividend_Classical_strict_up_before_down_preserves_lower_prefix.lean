-- Prove2me | Theorems.Thm_AvramDividend_Classical_strict_up_before_down_preserves_lower_prefix
-- name    : AvramDividend.Classical.strict_up_before_down_preserves_lower_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:53:06.74184+00:00
-- url     : https://prove2.me/theorems/9cb1a7d4-f9f8-4c3a-b572-24150399fc94
-- title:
--   Successful strict two-sided upper exit implies survival above the lower level throughout the prefix
-- statement:
--   For any strict upward and downward first-passage clocks of a Lévy path, if the upper clock is strictly before the lower clock then at every earlier deterministic time t the path value is at least the lower threshold. Otherwise the witnessing lower crossing at t forces the lower passage clock to be at most t, contradicting the strict order. This elementary but exact named-clock event inclusion converts the standard q-scale two-sided upper-first exit payoff into the lower ordinary prefix-survival payoff used in the stopped-dividend record sandwich.
-- source:
--   Order of first-passage stopping times; interface between Avram Palmowski Pistorius (2007) equation (3.6) and the first-record reflected survival sandwich.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.strict_up_before_down_preserves_lower_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u d : ℝ) (ω : Ω)
    (hUp : twoSidedExitUpTime X u ω <
      twoSidedExitDownTime X d ω) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < twoSidedExitUpTime X u ω →
      d ≤ X.X t ω := by sorry
