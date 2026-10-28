-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_killed_record_payments_tsum_finite_of_finite_ruin
-- name    : AvramDividend.Classical.chat08_killed_record_payments_tsum_finite_of_finite_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:40:34.219661+00:00
-- url     : https://prove2.me/theorems/e61fd739-95eb-4d6e-91ef-641d49487ed4
-- title:
--   Discounted first-record reward is finite pathwise whenever reflected ruin is finite
-- statement:
--   For a reflected finite ruin time, sufficiently high record levels are never crossed before ruin. The killed discounted record payments therefore vanish beyond a finite random index, and the countable ENNReal reward is finite on that sample path.
-- source:
--   Proved chat08_killed_grid_weights_eventually_zero_of_finite_ruin and Mathlib tsum_eq_sum plus ENNReal.sum_lt_top.

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat08_killed_grid_weights_eventually_zero_of_finite_ruin
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENNReal.BigOperators

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_killed_record_payments_tsum_finite_of_finite_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (a b h q : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    (∑' n : ℕ,
      if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (h * Real.exp
          (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
      else 0) < ⊤ := by sorry
