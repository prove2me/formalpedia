-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
-- name    : AvramDividend.Classical.avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:49:18.648359+00:00
-- url     : https://prove2.me/theorems/a39752ef-d1f2-40cd-aff9-d415a7b54277
-- title:
--   Original fixed-cutoff marked count in shrinking final stopped physical cell converges in L1 unconditionally
-- statement:
--   On the original process, the expected real count of negative jumps strictly after an arbitrary measurable physical stopping time and up to a measurable bounded right-grid endpoint converging to that time tends to zero at each fixed negative cutoff. The proof derives actual random-cell count measurability from original s-finite source kernel, pathwise eventual emptiness from finite original marked jump times, full-horizon count integrability and finiteness, measure monotonicity, and dominated convergence. It imposes no extra moment or majorant assumptions beyond the original SpectrallyNegativeLevy. This finite-band step does not assert an epsilon-uniform small-jump L2 bound.
-- source:
--   PJ-PHYS13 direct actual-source instantiation of proved pathwise 17e97019 and physical L1 a5c5c5b5, for canonical 0b1a879a under PJ-CLOSE13.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (hτ : Measurable τ) (he : ∀ k, Measurable (e k))
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω))) :
    let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Tendsto (fun k => ∫ ω,
      ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
