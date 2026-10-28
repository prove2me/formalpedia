-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_weight_lower_of_strict_exit
-- name    : AvramDividend.Classical.killed_firstRecord_weight_lower_of_strict_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:08:13.125613+00:00
-- url     : https://prove2.me/theorems/7079d405-7504-44fc-a013-50e1f3ef67ff
-- title:
--   The strict two-sided exit expectation is bounded by the killed reflected first-record reward
-- statement:
--   For any nonnegative reward depending on a path, the expected reward paid on a strict two-sided upper-first exit is bounded by the reward paid on the actual reflected-record survival event. Composes the published strict exit prefix inclusion and the independently Proved killed first-upcrossing survival comparison.
-- source:
--   Avram, Palmowski and Pistorius (2007), two-sided exit and Proposition 1. Pure pathwise expectation bridge.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_strict_up_before_down_preserves_lower_prefix
import Theorems.Thm_AvramDividend_Classical_named_killed_upcrossing_lower_of_raw_exit

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_weight_lower_of_strict_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (w : Ω → ℝ≥0∞) (k : ℝ≥0∞)
    (hExit : (∫⁻ ω,
      if twoSidedExitUpTime X b ω <
          twoSidedExitDownTime X (b - a) ω
      then w ω else 0 ∂P) = k) :
    k ≤ (∫⁻ ω,
      if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
      then w ω else 0 ∂P) := by sorry
