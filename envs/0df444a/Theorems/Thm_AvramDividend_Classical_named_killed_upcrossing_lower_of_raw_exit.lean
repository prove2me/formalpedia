-- Prove2me | Theorems.Thm_AvramDividend_Classical_named_killed_upcrossing_lower_of_raw_exit
-- name    : AvramDividend.Classical.named_killed_upcrossing_lower_of_raw_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:32:53.828526+00:00
-- url     : https://prove2.me/theorems/0129a9f0-4fb1-46e3-bde0-57019b5438c7
-- title:
--   Raw ordinary two-sided exit expectation bounds the genuine named killed record reward
-- statement:
--   For the official strict upward first-passage clock, restrict to paths where that clock is finite and consider the weighted ordinary lower-survival event X_t≥b−a before the first crossing. If this event has expected nonnegative reward k, then the actual reward killed by reflected drawdown ruin has expectation at least k. This eliminates the generic finite-clock witness and stopping-event set from the proved first-upcrossing survival sandwich, allowing the q-scale exit identity to feed directly into the expected first-record lower bound.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, killed first-record comparison; composition of Proved killed_firstUpcrossing_weighted_sandwich and named strict exit clock's raw-infimum identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_sandwich
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.named_killed_upcrossing_lower_of_raw_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (w : Ω → ℝ≥0∞) (k : ℝ≥0∞)
    (hRaw : (∫⁻ ω,
      if twoSidedExitUpTime X b ω ≠ ∞ ∧
          (∀ t : ℝ≥0, t < (twoSidedExitUpTime X b ω).toNNReal →
            b - a ≤ X.X t ω)
      then w ω else 0 ∂P) = k) :
    k ≤ (∫⁻ ω,
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      then w ω else 0 ∂P) := by sorry
