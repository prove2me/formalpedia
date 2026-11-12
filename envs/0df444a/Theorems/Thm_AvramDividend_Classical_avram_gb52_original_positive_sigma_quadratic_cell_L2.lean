-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb52_original_positive_sigma_quadratic_cell_L2
-- name    : AvramDividend.Classical.avram_gb52_original_positive_sigma_quadratic_cell_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:27:04.447284+00:00
-- url     : https://prove2.me/theorems/bbe6a90e-3e3b-4fab-88b3-564b6f0d3f07
-- title:
--   Positive-sigma original Gaussian quadratic cell residual has sharp squared-mesh rate
-- statement:
--   For the original Levy process with zero jump measure and positive Gaussian coefficient, the centred-square intrinsic Gaussian increment over a deterministic cell has an integrable square. Its expected square is bounded by eight times sigma to the fourth times the squared cell width. This combines the proved original Gaussian fourth-moment estimate with the original bounded quadratic-cell transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb52_original_positive_sigma_quadratic_cell_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s Δ : ℝ≥0) :
    let Z : Ω → ℝ := fun ω =>
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    Integrable (fun ω => (Z ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) ^ 2) P ∧
      (∫ ω, (Z ω ^ 2 - (Δ : ℝ) * X.σ ^ 2) ^ 2 ∂P) ≤
        8 * X.σ ^ 4 * (Δ : ℝ) ^ 2 := by
  sorry
