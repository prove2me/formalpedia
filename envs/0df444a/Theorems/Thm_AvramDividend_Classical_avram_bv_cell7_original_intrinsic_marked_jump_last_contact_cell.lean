-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_intrinsic_marked_jump_last_contact_cell
-- name    : AvramDividend.Classical.avram_bv_cell7_original_intrinsic_marked_jump_last_contact_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:57:16.059924+00:00
-- url     : https://prove2.me/theorems/84c337a5-9afb-4498-9be0-6c3fb589c7b9
-- title:
--   Original physical-grid intrinsic marked jump integral isolates its last contact cell
-- statement:
--   For the actual original Lévy path, every measurable nonnegative marked jump source splits into the sum over the first m genuine stopped physical cells and the one final ruin/horizon contact cell; the stopped terminal is explicit and no stochastic surrogate is used.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_intrinsic_marked_jump_last_contact_cell
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
      (∑ i ∈ Finset.range m,
        (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1))))) +
      (∫⁻ p, F p ∂N (Ioc (u m) (u (m + 1)))) := by sorry
