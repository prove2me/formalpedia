-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable
-- name    : AvramDividend.Classical.avram_wave3_01_fresh_reflected_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:41:21.441029+00:00
-- url     : https://prove2.me/theorems/b0df9a24-b63e-4018-b287-85892d1d7532
-- title:
--   Borel measurability of genuine future reflected-killed first-record discounted path reward
-- statement:
--   For any deterministic countable time schedule and any original real path f on nonnegative times, form the strict first upward-record clock of the centred path f-f(0) at b and the strict drawdown-ruin clock at a using the countably sampled running supremum of f-f(0). Then the q-discounted first-record payoff killed when the reflected drawdown ruins first is Borel measurable as a functional of the entire path in the product sigma algebra. Unlike ordinary two-sided exit measurability, the lower clock is the actual reflected-drawdown ruin, so the result is the missing measurable future reward for the source stopped-history strong Markov factorisation used to prove the true reflected record semigroup and pure-jump q-scale C1 regularity.
-- source:
--   Avram, Palmowski and Pistorius (2007), reflected dividend passage; accepted path_countable_drawdown_ruin_clock_measurable and original first record path measurable lemmas.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_path_countable_drawdown_ruin_clock_measurable

open MeasureTheory
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave3_01_fresh_reflected_reward_measurable
    (samples : ℕ → ℝ≥0) (a b q : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      let ρ : ℝ≥0∞ := ⨅ i : ℕ,
        if b < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
      let σ : ℝ≥0∞ := ⨅ i : ℕ,
        if f (samples i) - f 0 -
          (⨆ j : ℕ,
            if samples j ≤ samples i then
              ENNReal.ofReal (f (samples j) - f 0)
            else 0).toReal < -a then
          (samples i : ℝ≥0∞) else ⊤
      if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
      else 0) := by sorry
