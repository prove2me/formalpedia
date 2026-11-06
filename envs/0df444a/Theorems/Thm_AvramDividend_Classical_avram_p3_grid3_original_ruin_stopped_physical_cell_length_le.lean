-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:15:27.143855+00:00
-- url     : https://prove2.me/theorems/4ded2370-1d4f-45cb-b619-95c3814ba440
-- title:
--   Actual ruin-stopped original physical mesh cells are bounded by deterministic refinement scale
-- statement:
--   Clamp a uniform physical time grid at the literal original Lévy controlled ruin time, with cap horizon T. Every adjacent stopped cell has nonnegative NNReal length at most the deterministic T/(m+1), including the cell crossing ruin and the final horizon cell. Together with deterministic cell length tending zero this proves the random stopped-grid mesh scale required for source-local C1 convergence.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_exact_cell_length
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (m i : ℕ) (hi : i < m + 1) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u (i + 1) - u i ≤ T / (m + 1) := by sorry
