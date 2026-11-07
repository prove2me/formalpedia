-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
-- name    : AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:45:40.423202+00:00
-- url     : https://prove2.me/theorems/b7f96257-9e0a-40c3-bc0f-29dea0f1f5eb
-- title:
--   Exact intrinsic Lévy marked-jump integral partition on the original stopped dividend physical grid
-- statement:
--   For actual original Lévy X and dividend path D, the original jump-mark lintegral is the exact sum of all half-open intrinsic jump cells on the physical ruin/horizon clipped grid. The grid has genuine zero start and stopped terminal, and the last contact cell is retained exactly.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
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
        (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by sorry
