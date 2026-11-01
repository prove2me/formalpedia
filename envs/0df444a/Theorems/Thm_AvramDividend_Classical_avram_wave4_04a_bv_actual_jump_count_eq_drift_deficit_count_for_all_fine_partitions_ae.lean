-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:32:54.01437+00:00
-- url     : https://prove2.me/theorems/cc7abaca-d041-4ec1-ae5f-0c8d8f5772aa
-- title:
--   Actual BV Lévy jump counting measure equals observable original drift-deficient grid count for every fine partition almost surely
-- statement:
--   For an original adapted finite-activity bounded-variation spectrally-negative Lévy source, on one original-probability-one event there exists a strictly positive random mesh threshold such that for all finite strictly increasing partitions of [0,T] finer than that threshold, the literal original-path intrinsic N_X((0,T] × ℝ) equals the exact number of grid cells whose source X increments fall strictly below deterministic source drift. This provides the pathwise identification needed to pass the genuine source grid Poisson counting limit to N_X, without equal-law substitution.
-- source:
--   Combine canonically Proved original-X short-partition jump occupancy count 7df2397f-dc8a-4263-a8ea-c3e656b0de16 and original-X jump-occupied cell iff drift deficit 4426d791-7c3f-4ad0-bb9e-c0c564bfef20. For each strict partition with grid 0=0 and grid n=T, each occupied cell has u∈(0,T], so the two original index sets coincide, then rewrite in the exact N_X ENNReal equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
        StrictMono grid → grid 0 = 0 → grid n = T →
        (∀ i : ℕ, i < n →
          dist (grid i) (grid (i + 1)) < δ) →
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) =
        ({i : ℕ | i < n ∧
          X.X (grid (i + 1)) ω - X.X (grid i) ω <
            X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))}.ncard :
          ENNReal) := by sorry
