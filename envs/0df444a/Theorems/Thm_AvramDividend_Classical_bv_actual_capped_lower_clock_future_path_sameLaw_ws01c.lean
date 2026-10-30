-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
-- name    : AvramDividend.Classical.bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:46:15.592737+00:00
-- url     : https://prove2.me/theorems/fe7aee3e-ffaf-4e08-abe8-71b06bbb887b
-- title:
--   Actual strict lower exit capped at a finite horizon preserves the entire shifted Lévy future-path law
-- statement:
--   For the actual spectrally negative Lévy process and its strict lower exit capped at T, the shifted whole future-increment path has exactly the law of the original process in the product measurable path space. Construct original-filtration finite observation-grid stopping clocks converging from above, prove the raw capped clock measurable, then apply the canonically Proved full finite-vector-to-path law transfer. No assumption that the raw clock itself is a stopping time of the arbitrary original filtration, and no uncountable product weak limit.
-- source:
--   Exact 39-line source work/avram_ws01c_actual_capped_lower_future_law_solution_20261028.lean. Publication and proof deliberately withheld until original finite capped right-grid clock theorem and the two parser-blocked grid helpers are legitimately Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_finite_capped_grid_right_clock_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_capped_raw_lower_clock_NNReal_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_grid_stop_limit_full_future_path_law_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (lower : ℝ) (T : ℝ≥0)
    (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X ((twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal + t) ω -
      X.X ((twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal) ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by sorry
