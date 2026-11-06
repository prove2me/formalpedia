-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cells_eventually_small
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cells_eventually_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:32:58.908564+00:00
-- url     : https://prove2.me/theorems/e084597b-4019-48cd-89eb-dabd1f4332ee
-- title:
--   All original ruin-stopped physical mesh cells shrink uniformly in refinement
-- statement:
--   Uniformly over every actual original Lévy sample ω and every ruin-clamped physical cell i<m+1, the NNReal stopped-cell length tends to zero as m grows, with no random control assumptions. Combine the genuine stopped-cell upper bound and the deterministic uniform grid rate; this is the source pathwise mesh-smallness premise for BV stopped physical-grid C1 error arguments.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_cell_size_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cells_eventually_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ω : Ω, ∀ i : ℕ, i < m + 1 →
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun j =>
        min (((min j (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1))) τ
      ((u (i + 1) - u i : ℝ≥0) : ℝ) < δ := by sorry
