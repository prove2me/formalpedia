-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_flat_after_contact
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_flat_after_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:15:40.377464+00:00
-- url     : https://prove2.me/theorems/831959c2-00a4-46af-9681-45d0e20771fd
-- title:
--   Actual original ruin-clamped physical clock stays frozen after first stopped-time contact
-- statement:
--   For the actual original spectrally-negative Levy sample and ruin-clamped physical clock, once any grid point first reaches tau=min(ruinTime,horizon), every later point remains exactly at tau. Consequently all later grid cells are zero-length, which separates the single possible boundary-crossing cell from the interior strict pre-ruin Stieltjes source budget.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_flat_after_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ∀ i j : ℕ, i ≤ j → u i = τ → u j = τ := by sorry
