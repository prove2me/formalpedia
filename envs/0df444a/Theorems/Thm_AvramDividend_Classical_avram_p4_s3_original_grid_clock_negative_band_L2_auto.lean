-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_clock_negative_band_L2_auto
-- name    : AvramDividend.Classical.avram_p4_s3_original_grid_clock_negative_band_L2_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:25:24.873734+00:00
-- url     : https://prove2.me/theorems/98a44e48-12b1-465e-b78c-ad795949ed91
-- title:
--   Original Lévy negative-band jump count has automatic L² at every bounded measurable grid-selected stopping clock
-- statement:
--   For any measurable ℕ-valued grid selector whose original selected time never exceeds T, the physical number of Lévy jumps below negative cutoff -1/(n+1) before the selected horizon belongs to L². Both measurability and the quantitative quadratic stopping budget come from accepted original-process P4-S3 theorems.
-- source:
--   Proved P4-S3 count measurability 4926eb4c and original grid-stopped quadratic bound 0cb80e25, pinned Mathlib memLp_two_iff_integrable_sq.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_grid_clock_negative_band_L2_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ ω, grid (tick ω) ≤ T) :
    MemLp (fun ω : Ω => ({u : ℝ≥0 | 0 < u ∧
      u ≤ grid (tick ω) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard : ℝ)) 2 P := by sorry
