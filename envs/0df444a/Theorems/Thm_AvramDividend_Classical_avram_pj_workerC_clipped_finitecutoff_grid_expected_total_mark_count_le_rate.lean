-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_clipped_finitecutoff_grid_expected_total_mark_count_le_rate
-- name    : AvramDividend.Classical.avram_pj_workerC_clipped_finitecutoff_grid_expected_total_mark_count_le_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:30:50.046951+00:00
-- url     : https://prove2.me/theorems/44f735ca-f3e6-458a-b8d7-8c3fbd419c32
-- title:
--   Expected total intrinsic negative cutoff jump count across every actual randomly ruin-clipped physical mesh is uniformly bounded by deterministic horizon times finite-band Lévy rate
-- statement:
--   For original spectrally negative Lévy X, true random clipped grid u_i=min(g_i,rho) with rho<=n and any measurable negative mark set B bounded away from zero, the expectation of the sum of the marked jump counting measure on each actual grid cell is uniformly bounded by n * X.nu(B). It holds for infinite-activity unbounded-variation purejump processes; the finite cutoff rate is derived from B and no artificial independence or full-negative finite-intensity assumption is used. It gives an integrable uniform dominator for same-grid negative-mark jump compensation, including final partial cell.
-- source:
--   Proved 09bdd280 intrinsic marked partition, Proved physical grid monotonicity and endpoint, Proved 34dbea70 full horizon expected negative separated mark count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_clipped_finitecutoff_grid_expected_total_mark_count_le_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Ω → ℝ≥0) (n m : ℕ)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : Ω → ℕ → ℝ≥0 := fun ω i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let J : Ω → Set ℝ≥0 → ℝ≥0∞ := fun ω I =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (I ×ˢ B)
    (∫⁻ ω, (∑ i ∈ Finset.range (m + 1),
      J ω (Ioc (u ω i) (u ω (i+1)))) ∂P) ≤
    ((n : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
