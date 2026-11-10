-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess24_original_full_negative_count_grid_collision_L1_vanish
-- name    : AvramDividend.Classical.avram_bv_excess24_original_full_negative_count_grid_collision_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:48:44.773209+00:00
-- url     : https://prove2.me/theorems/cc884bf4-23f2-40f1-8796-98526a02146c
-- title:
--   Original BV finite-activity full-horizon negative-jump collision excess tends to zero in mean on cofinal physical grids
-- statement:
--   The full original spectrally negative BV jump-count N_X((0,T]×ℝ) has finite expected count exactly Tν((−∞,0)) by Proved 2fdbada6. For any genuine full-horizon strictly increasing physical grid with mesh tending to zero, Proved 7df2397f says eventually the original occupied-cell count equals N_X pathwise almost surely, so their nonnegative difference is dominated by the integrable original N_X. Proved 2811485c supplies the dominated-convergence L1 limit. Only measurability of the exact occupancy difference remains explicit, and is separately available through original-source increment deficits. This full-grid error dominates the strict-prefix collision term in root-connected f3f336fd and 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess22_original_source_collision_lintegral_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_grid_count_eq_source_jump_count_ae_short_partition
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_fullmark_all_time_intervals_exact_rate
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess24_original_full_negative_count_grid_collision_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0) (cells : ℕ → ℕ)
    (hStrict : ∀ n, StrictMono (grid n))
    (hZero : ∀ n, grid n 0 = 0)
    (hEnd : ∀ n, grid n (cells n) = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        ∀ i : ℕ, i < cells n →
          dist (grid n i) (grid n (i + 1)) < δ)
    (hDiffMeas : ∀ n, Measurable (fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      ({i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
      u ≤ T ∧ 0 < u ∧
      X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      u ∈ Ioc (grid n i) (grid n (i + 1))}.ncard : ℝ≥0∞))) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      ({i : ℕ | i < cells n ∧ ∃ u : ℝ≥0,
      u ≤ T ∧ 0 < u ∧
      X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      u ∈ Ioc (grid n i) (grid n (i + 1))}.ncard : ℝ≥0∞) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
