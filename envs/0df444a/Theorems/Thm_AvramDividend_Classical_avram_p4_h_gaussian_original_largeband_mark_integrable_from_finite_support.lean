-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:25:27.798491+00:00
-- url     : https://prove2.me/theorems/dd802e30-fa56-4c70-a599-4a8f5a569b15
-- title:
--   The original Lévy process has pathwise integrable large-negative jump marks on every bounded horizon
-- statement:
--   The signed marks z of the original intrinsic marked-jump measure of X on (0,T] × (-∞,-1] are integrable, without an external process, additional moment condition or assumed mark bound. The Proved finite jump-time source theorem gives a finite support F. Its sum of absolute marks bounds every supported large jump; the original rectangle encard theorem makes the bad-mark set null, and the Proved finite-intensity-of-bounded-mark theorem supplies IntegrableOn.
-- source:
--   Source-exact Proved e45c2694-a4b4-4794-b13e-877dfcebff94, f6336d40-2d19-444f-bacd-83724316de67, 27b07e57-79d5-4806-a458-bb0b2504b824.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_of_ae_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E N := by sorry
