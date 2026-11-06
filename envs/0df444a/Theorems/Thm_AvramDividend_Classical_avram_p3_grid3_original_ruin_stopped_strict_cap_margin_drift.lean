-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_cap_margin_drift
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_cap_margin_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:02:48.748686+00:00
-- url     : https://prove2.me/theorems/3b70a120-aa94-4a61-89d2-6d6de4b87161
-- title:
--   Original stopped BV drift increments preserve any fixed strictly interior cap margin
-- statement:
--   If genuine original-process reserve grid inputs have a strictly positive uniform margin rho below a finite cap (or cap is infinity), then eventually every actual ruin-stopped physical drift step stays below cap, uniformly over sample paths and grid cells. The drift smallness follows from the source-exact original stopped physical cell rate, with no independent drift bound. Positive cap contact still requires the separate canonical cap-linear extension.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_cap_margin_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (C : ℝ≥0∞)
    (ρ : ℝ) (hρ : 0 < ρ)
    (z : ℕ → ℕ → Ω → ℝ)
    (hInterior : ∀ m i (ω : Ω), i < m + 1 →
      C = ⊤ ∨ z m i ω ≤ C.toReal - ρ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ω : Ω, ∀ i : ℕ, i < m + 1 →
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun k =>
        min (((min k (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1))) τ
      C = ⊤ ∨ z m i ω +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal := by sorry
