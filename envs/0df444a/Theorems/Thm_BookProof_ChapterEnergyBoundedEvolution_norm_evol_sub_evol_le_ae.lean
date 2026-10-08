-- Prove2me | Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_norm_evol_sub_evol_le_ae
-- name    : BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:46:34.350281+00:00
-- url     : https://prove2.me/theorems/3d3368a1-6849-4504-a16c-78def7f5ecf6
-- title:
--   `BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae` {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) : ∀ᵐ x ∂μ, ‖evol E t f x - evol E s f x‖ ≤ (|t - s| * Emax) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBoundedEvolution`.
--
--   `BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae` {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) : ∀ᵐ x ∂μ, ‖evol E t f x - evol E s f x‖ ≤ (|t - s| * Emax) * ‖f x‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae`.

-- Generated from ChapterEnergyBoundedEvolution.lean — theorem BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae
import Definitions.Def_ChapterEnergyBandDecomposition
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
open BookProof.ChapterEnergyBoundedEvolution



open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

theorem BookProof.ChapterEnergyBoundedEvolution.norm_evol_sub_evol_le_ae {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) :
    ∀ᵐ x ∂μ, ‖evol E t f x - evol E s f x‖ ≤ (|t - s| * Emax) * ‖f x‖ := by sorry
