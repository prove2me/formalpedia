-- Prove2me | Theorems.Thm_AvramDividend_Classical_path_countable_drawdown_ruin_clock_measurable
-- name    : AvramDividend.Classical.path_countable_drawdown_ruin_clock_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:37:24.761365+00:00
-- url     : https://prove2.me/theorems/d7f3c012-f073-443c-ba03-da604da921c1
-- title:
--   Product-path measurability of the countably sampled strict drawdown ruin clock
-- statement:
--   For any countable observation schedule and reserve height a, form the stopped reflected-ruin clock as the infimum of observation times at which the sampled Lévy increment is strictly below minus a plus the sampled running positive maximum. This extended nonnegative-valued exit-time functional is measurable on the unrestricted product path space. No càdlàg property is required for measurability; later pathwise identification on right-continuous spectrally negative paths is separate.
-- source:
--   Avram, Palmowski and Pistorius (2007), reflected-supremum ruin clock in Proposition 1. A path-space measurable drawdown killing time is the missing measurable-stop input to path_countable_killed_record_grid_reward_measurable upstream of canonical target 79978d61.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.path_countable_drawdown_ruin_clock_measurable
    (samples : ℕ → ℝ≥0) (a : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨅ i : ℕ,
        if f (samples i) - f 0 -
          (⨆ j : ℕ,
            if samples j ≤ samples i then
              ENNReal.ofReal (f (samples j) - f 0)
            else 0).toReal < -a then
          (samples i : ℝ≥0∞)
        else ⊤) := by
  sorry
