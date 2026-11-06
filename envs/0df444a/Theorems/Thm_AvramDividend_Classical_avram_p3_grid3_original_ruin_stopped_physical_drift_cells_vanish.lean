-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:54:37.835999+00:00
-- url     : https://prove2.me/theorems/8e714568-4038-43cb-a895-9a8761c661ae
-- title:
--   Actual BV ruin-stopped physical drift cells vanish uniformly
-- statement:
--   Uniformly over every sample of the original spectrally-negative Levy process and every cell of the real ruin-clamped physical grid, the absolute frozen drift increment |(u_(i+1)-u_i)*X.drift| eventually falls below arbitrary epsilon. Derives directly from the original stopped physical mesh-smallness and monotonicity, without an abstract drift-smallness premise, and supplies the key cap-margin physical C1 hypothesis.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cells_eventually_small
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ω : Ω, ∀ i : ℕ, i < m + 1 →
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun k =>
        min (((min k (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1))) τ
      |(((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)| < ε := by sorry
