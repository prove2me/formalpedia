-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
-- name    : AvramDividend.Classical.avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:16:58.752029+00:00
-- url     : https://prove2.me/theorems/847d6163-c5fe-431f-af86-676883fe07d5
-- title:
--   Original Lévy marked count on a bounded random stopped clock exactly telescopes across true clipped physical mesh including final partial cell
-- statement:
--   For any original spectrally negative Lévy jump-count measure and measurable mark set B, the finite sum of all actual marked jump counts over the canonical clipped physical grid u_i=min(i*n/(m+1),rho) equals the marked jump count on (0,rho]. The identity is exact even at the randomly stopped partial final cell and needs no finite intensity assumption; it uses the same original X for every cell. This provides a rigorous same-grid counting identity for the uncompensated part of J and the annular linear L.
-- source:
--   Proved 09bdd280 original marked count grid telescoping, Proved original physical grid monotonicity and exact clipped endpoint results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_marked_count_grid_telescoping
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_trueclock_clipped_marked_grid_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ρ : Ω → ℝ≥0) (n m : ℕ)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (B : Set ℝ) (hB : MeasurableSet B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (I ×ˢ B)
    (∑ i ∈ Finset.range (m + 1), J (Ioc (u i) (u (i + 1)))) =
      J (Ioc 0 (ρ ω)) := by sorry
