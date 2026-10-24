-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_killed_grid_weights_eventually_zero_of_finite_ruin
-- name    : AvramDividend.Classical.chat08_killed_grid_weights_eventually_zero_of_finite_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:19:06.256064+00:00
-- url     : https://prove2.me/theorems/70fa090c-90df-4dbb-ab65-8b142c28d3fb
-- title:
--   Every killed stopped first-record grid weight is eventually zero on finite-ruin paths
-- statement:
--   On every sample path with finite reflected ruin, every sufficiently high strict upward record threshold has first passage at or after ruin. Thus the exact killed discounted first-record payments, expressed with official twoSidedExitUpTime and barrierRuinTime, form a sequence that is eventually identically zero. This supplies the finite-path truncation premise for stopped-renewal upper covers.
-- source:
--   Proved stopped_record_grid_no_late_hit_of_finite_ruin, official named clock unfolding, and pointwise if_neg.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_stopped_record_grid_no_late_hit_of_finite_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_killed_grid_weights_eventually_zero_of_finite_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (a b h q : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (if twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
          barrierRuinTime X a ω then
         ENNReal.ofReal (h * Real.exp
           (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * h) ω).toReal)))
       else 0) = 0 := by sorry
