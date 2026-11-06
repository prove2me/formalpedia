-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:18:33.544395+00:00
-- url     : https://prove2.me/theorems/970d5a93-2758-4734-ac13-d9e7ea536ad5
-- title:
--   Exact original large negative jump integral equals source jump series under its genuine pathwise integrability
-- statement:
--   For the original Levy X, reduce its published uncompensated large-jump integral exactly to its own actual negative jump-time series. The sole extra hypothesis is integrability of that exact original marked counting measure on the large band. The source support is proved finite separately; discharging this integrability is now a precise remaining original-process obligation. No unrelated process or Gaussian source is posited.
-- source:
--   Published P4-H original large negative jump integral Definition 4c0b840b, Proved signed intrinsic integral-to-source-jump tsum c1360947, and pinned Mathlib integrableOn_indicator_iff/integral_indicator.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_real_integral_eq_source_jump_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) E N →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
        ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
          E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := by sorry
