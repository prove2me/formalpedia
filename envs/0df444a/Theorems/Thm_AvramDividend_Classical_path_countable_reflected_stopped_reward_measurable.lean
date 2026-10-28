-- Prove2me | Theorems.Thm_AvramDividend_Classical_path_countable_reflected_stopped_reward_measurable
-- name    : AvramDividend.Classical.path_countable_reflected_stopped_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:14:57.513985+00:00
-- url     : https://prove2.me/theorems/d83660d4-f59f-4dcf-92e0-b4b5053d9831
-- title:
--   Global product-path measurability of the full countably sampled stopped reflected reward
-- statement:
--   For arbitrary real paths indexed by nonnegative times, a countable observation schedule, a sequence of dividend-payment grids with nonnegative weights, and a positive-barrier height, define each sampled running record, the strict sampled drawdown killing clock and the killed positive record increments over every payment cell. The supremum over finite payment horizons and all grids is Borel measurable on the unrestricted product path space. This is the globally measurable payoff needed by the finite-stopping strong-Markov theorem before identifying it with the genuine pathwise stopped Stieltjes reward on spectrally negative cadlag Levy paths.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and Equation (5.1). Direct composition of the already Proved sampled-drawdown-clock measurability and killed-record-grid-reward measurability, for the final strong-Markov path payoff in target 79978d61.

import Theorems.Thm_AvramDividend_Classical_path_countable_killed_record_grid_reward_measurable
import Theorems.Thm_AvramDividend_Classical_path_countable_drawdown_ruin_clock_measurable

open MeasureTheory
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.path_countable_reflected_stopped_reward_measurable
    (samples : ℕ → ℝ≥0) (mesh : ℕ → ℕ → ℝ≥0)
    (weights : ℕ → ℕ → ℝ≥0∞) (a : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
        if (mesh n (k + 1) : ℝ≥0∞) <
          (⨅ i : ℕ,
            if f (samples i) - f 0 -
              (⨆ j : ℕ,
                if samples j ≤ samples i then
                  ENNReal.ofReal (f (samples j) - f 0)
                else 0).toReal < -a then
              (samples i : ℝ≥0∞)
            else ⊤) then
          weights n k * ENNReal.ofReal
            ((⨆ i : ℕ,
                if samples i ≤ mesh n (k + 1) then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal -
              (⨆ i : ℕ,
                if samples i ≤ mesh n k then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal)
        else 0) := by
  sorry
