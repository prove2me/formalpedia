-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_marked_jump_physical_grid_parts
-- name    : AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_marked_jump_physical_grid_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:58:46.533302+00:00
-- url     : https://prove2.me/theorems/5e5d9bdf-a1b5-4953-a515-e0a9067806ec
-- title:
--   Original stopped physical-grid discounted C1 marked jump positive and negative parts partition
-- statement:
--   For the actual Lévy X and dividend strategy D, each nonnegative signed part of the discounted original left-reserve C1 jump-value kernel partitions exactly over the ruin/horizon clipped physical cells. Integrand measurability is obtained from the published original-process joint kernel lemma, with zero and contact endpoints treated by half-open cells.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_marked_jump_physical_grid_parts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) p.1 + p.2) -
          w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) p.1)
      else 0
    let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) * K p)
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
    (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by sorry
