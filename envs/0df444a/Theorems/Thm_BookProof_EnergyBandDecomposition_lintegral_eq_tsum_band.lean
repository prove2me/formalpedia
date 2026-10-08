-- Prove2me | Theorems.Thm_BookProof_EnergyBandDecomposition_lintegral_eq_tsum_band
-- name    : BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:45:47.505976+00:00
-- url     : https://prove2.me/theorems/a0690bd9-57b3-4a8d-83c2-f6923c771380
-- title:
--   `BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band` [MeasurableSpace X] {μ : Measure X} (hε : 0 < ε) (hE : Measurable E) (f : X → ℂ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∑' k :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBandDecomposition`.
--
--   `BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band` [MeasurableSpace X] {μ : Measure X} (hε : 0 < ε) (hE : Measurable E) (f : X → ℂ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∑' k : ℤ, ∫⁻ x in band E ε k, ‖f x‖ₑ ^ 2 ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band`.

-- Generated from ChapterEnergyBandDecomposition.lean — theorem BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition



open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

theorem BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band [MeasurableSpace X] {μ : Measure X} (hε : 0 < ε)
    (hE : Measurable E)
    (f : X → ℂ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∑' k : ℤ, ∫⁻ x in band E ε k, ‖f x‖ₑ ^ 2 ∂μ := by sorry
