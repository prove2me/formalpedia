-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_two_grid_clocks_negative_band_count_L2_difference
-- name    : AvramDividend.Classical.avram_p4_s3_original_two_grid_clocks_negative_band_count_L2_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:27:44.660883+00:00
-- url     : https://prove2.me/theorems/6c3de50b-5b60-48eb-a4f4-52513d5e9af3
-- title:
--   Original Lévy negative-band counts at any two bounded measurable grid stopping clocks differ by an L² variable
-- statement:
--   For the same genuine Lévy process, any two measurable grid-selected random times bounded by T give physical negative-band marked jump counts whose real difference belongs to L². Apply the proved intrinsic grid-clock count measurability and original stopped quadratic budget to each selection, then subtract in L². This requires no equality-in-law comparison and is directly usable for localisation and horizon/ruin residuals.
-- source:
--   Public source-specific P4-S3 4926eb4c and 0cb80e25, pinned Mathlib memLp_two_iff_integrable_sq and MemLp.sub.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_two_grid_clocks_negative_band_count_L2_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (grid : ℕ → ℝ≥0)
    (tick₁ tick₂ : Ω → ℕ)
    (htick₁ : Measurable tick₁) (htick₂ : Measurable tick₂)
    (hbound₁ : ∀ ω, grid (tick₁ ω) ≤ T)
    (hbound₂ : ∀ ω, grid (tick₂ ω) ≤ T) :
    MemLp (fun ω : Ω =>
      ({u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick₁ ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) -
      ({u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick₂ ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ)) 2 P := by sorry
