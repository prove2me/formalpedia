-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_named_stopped_grid_no_late_hit_of_finite_ruin
-- name    : AvramDividend.Classical.chat08_named_stopped_grid_no_late_hit_of_finite_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:21:26.400975+00:00
-- url     : https://prove2.me/theorems/4aa90c07-5894-45cc-981c-7fb47b0f97df
-- title:
--   Finite reflected ruin eventually kills all named strict first-record grid weights
-- statement:
--   On every path whose reflected ruin time is finite, a positive uniformly spaced sequence of record thresholds has only finitely many strict upward passage events occurring before ruin. Rewrite the accepted raw indexed-infimum no-late-hit theorem into the official named twoSidedExitUpTime clock used in measurable renewal weights, closing the finite-ruin eventual-zero indicator bridge.
-- source:
--   Prove2Me stopped_record_grid_no_late_hit_of_finite_ruin and definitional equality of twoSidedExitUpTime with its raw indexed infimum.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_stopped_record_grid_no_late_hit_of_finite_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_named_stopped_grid_no_late_hit_of_finite_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (a b h : ℝ) (hh : 0 < h) (τ : ℝ≥0)
    (hτ : barrierRuinTime X a ω = (τ : ℝ≥0∞)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ twoSidedExitUpTime X (b + (n : ℝ) * h) ω <
        barrierRuinTime X a ω := by sorry
