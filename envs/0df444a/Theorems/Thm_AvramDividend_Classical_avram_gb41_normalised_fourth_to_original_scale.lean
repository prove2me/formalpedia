-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb41_normalised_fourth_to_original_scale
-- name    : AvramDividend.Classical.avram_gb41_normalised_fourth_to_original_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:42:12.214879+00:00
-- url     : https://prove2.me/theorems/7bb7dbe5-93c9-4a16-b3d3-e7115a039600
-- title:
--   Unnormalised fourth-moment bound for the original Gaussian increment
-- statement:
--   If the original centred increment divided by its positive Gaussian coefficient has fourth lintegral at most three times the squared interval, the unscaled increment has a finite fourth real expectation at most three sigma-to-fourth times the squared interval.
-- source:
--   Scaling ingredient for the original finite-cap centred-square Gaussian cell bound gb34, combining gb39 with the Proved stationary Gaussian fourth lintegral estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb41_normalised_fourth_to_original_scale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ) (σ Δ : ℝ) (hσ : 0 < σ)
    (hZ : Measurable Z)
    (hFourth : (∫⁻ ω, ENNReal.ofReal ((Z ω / σ) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * Δ ^ 2)) :
    Integrable (fun ω => Z ω ^ 4) P ∧
      (∫ ω, Z ω ^ 4 ∂P) ≤ 3 * σ ^ 4 * Δ ^ 2 := by sorry
