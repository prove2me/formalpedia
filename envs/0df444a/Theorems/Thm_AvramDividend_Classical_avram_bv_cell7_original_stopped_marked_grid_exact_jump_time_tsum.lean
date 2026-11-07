-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum
-- name    : AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:41:28.185467+00:00
-- url     : https://prove2.me/theorems/696752a3-6c7f-4ed5-acda-b566ac138f35
-- title:
--   Exact original intrinsic marked source as finite physical-grid sum of actual jump-time series
-- statement:
--   For the actual original Lévy path and dividend strategy, any nonnegative measurable intrinsic marked source integrated up to the stopped ruin/horizon terminal equals the finite sum over its exact physical-grid cells of the genuine mark-weighted jump-time tsums, including the final contact cell and excluding the time-zero jump.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
    (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
            F (v, Δ v) else 0) := by sorry
