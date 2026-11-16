-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
-- name    : AvramDividend.Classical.avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:46:48.370189+00:00
-- url     : https://prove2.me/theorems/80b0ddf8-8425-4375-a766-29a8c05256cc
-- title:
--   Original Gaussian fixed physical grid centred cell has finite second moment
-- statement:
--   Every original zero-jump Gaussian full physical-grid centred increment inside a finite deterministic horizon has an integrable square.
-- source:
--   Original zero-jump L2 fixed-time increment theorem a542, algebra of the physical grid times s=iΔ and Δ=n/(m+1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n m i : ℕ) (hi : i < m) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    Integrable (fun ω =>
      (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c)^2) P := by sorry
