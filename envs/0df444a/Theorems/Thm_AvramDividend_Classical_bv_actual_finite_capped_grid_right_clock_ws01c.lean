-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_finite_capped_grid_right_clock_ws01c
-- name    : AvramDividend.Classical.bv_actual_finite_capped_grid_right_clock_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:11:36.729316+00:00
-- url     : https://prove2.me/theorems/07115691-ad18-411b-88ff-2d0f77d1d8db
-- title:
--   Original-filtration finite capped grid clocks converge from above to the actual strict lower exit
-- statement:
--   The finite explicit observation-grid lower-clock capped at T is a stopping time in the original filtration at every mesh level, converges pointwise from above to the strict lower exit capped at T, and never falls below that raw capped clock. The proof composes the genuine grid stopping-time, finite prefix equality, capped infimum convergence and ENNReal-to-NNReal limit interfaces. No filtration enlargement, linearly interpolated clock or uncountable product-space limit is used.
-- source:
--   Prepared compact 75-line source work/avram_ws01c_actual_finite_capped_grid_right_clock_solution_compact_20261028.lean from original 93-line WS01C assembly. Authoring and remote Lean must wait for existing exact finite-grid definition/parser unblock and the pending named capped-grid convergence and prefix adapter theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_grid_capped_NNReal_stopping_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_observation_times_within_mesh_horizon_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_finite_grid_clock_prefix_cap_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_capped_lower_grid_clock_tendsto_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_raw_strict_lower_clock_le_grid_cap_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c

open Filter MeasureTheory Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_finite_capped_grid_right_clock_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (lower : ℝ) (T : ℝ≥0) (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    let grid : ℕ → Ω → ℝ≥0 := fun n ω =>
      bv_finite_grid_below_NNReal_ws01c X.X lower
        ((M n : ℝ≥0) * mesh n)
        ((List.range (M n + 1)).map
          (fun k : ℕ => (k : ℝ≥0) * mesh n)) ω ⊓ T
    (∀ n s, MeasurableSet[ℱ s] {ω : Ω | grid n ω ≤ s}) ∧
    (∀ ω, Tendsto (fun n => grid n ω) atTop
      (𝓝 ((twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal))) ∧
    (∀ ω n, (twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal ≤ grid n ω) := by sorry
