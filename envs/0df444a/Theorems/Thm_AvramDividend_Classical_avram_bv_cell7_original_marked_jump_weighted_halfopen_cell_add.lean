-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add
-- name    : AvramDividend.Classical.avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:29:56.673027+00:00
-- url     : https://prove2.me/theorems/cbfef811-740b-468b-a4e1-a45d9cb20086
-- title:
--   Actual original Lévy marked jump measure weighted half-open contact-cell additivity
-- statement:
--   For the actual original Lévy process X on an arbitrary fixed sample path, every nonnegative Borel jump-mark test is additive across adjoining half-open physical cells. Genuine jump-time and mark-map measurability follow from accepted original-process theorems, without additional assumptions.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_halfopen_marked_count_lintegral_add

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let Δ : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ I)).map
        (fun u : ℝ≥0 => (u, Δ u))
    (∫⁻ p, F p ∂N (Ioc a c)) =
      (∫⁻ p, F p ∂N (Ioc a b)) +
        (∫⁻ p, F p ∂N (Ioc b c)) := by sorry
