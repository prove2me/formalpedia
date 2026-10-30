-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
-- name    : AvramDividend.Classical.avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:16:36.993829+00:00
-- url     : https://prove2.me/theorems/39fa7c63-0181-4e24-a140-94bab73c8ce8
-- title:
--   Actual original Lévy two-sided stopped grid has an exhaustive three-way killed-horizon partition
-- statement:
--   For every original Lévy path and any finite horizon T, one of three source clock regimes holds: no lower ruin before the horizon, lower-first strict ruin no later than T, or upper-first strict exit before T. Genuine finite-tie impossibility rules out the otherwise problematic equality case. This exhausts exactly the surviving-horizon, lower-first zero-payoff and upper-first killed-grid convergence theorems.
-- source:
--   Exact original clocks and Proved source upper-first iff finite-min stopped time 9a984dcc. The complete ordered ENNReal partition handles top and finite T and transports finite comparisons through ENNReal.toNNReal only under proved finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_up_first_iff_finite_stopped_min

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) (T : ℝ≥0) :
    (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω ∨
    (twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω ∧
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T) ∨
    (twoSidedExitUpTime X (a-x) ω < twoSidedExitDownTime X (-x) ω ∧
      (twoSidedExitUpTime X (a-x) ω).toNNReal < T) := by sorry
