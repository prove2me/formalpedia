-- Prove2me | Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_norm_evol_apply
-- name    : BookProof.ChapterEnergyBoundedEvolution.norm_evol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:45:58.825567+00:00
-- url     : https://prove2.me/theorems/e048dfe9-e2bf-47b4-9b0b-db685061f7e2
-- title:
--   `BookProof.ChapterEnergyBoundedEvolution.norm_evol_apply` (t : ℝ) (f : X → ℂ) (x : X) : ‖evol E t f x‖ = ‖f x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBoundedEvolution`.
--
--   `BookProof.ChapterEnergyBoundedEvolution.norm_evol_apply` (t : ℝ) (f : X → ℂ) (x : X) : ‖evol E t f x‖ = ‖f x‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEnergyBoundedEvolution.norm_evol_apply`.

-- Generated from ChapterEnergyBoundedEvolution.lean — theorem BookProof.ChapterEnergyBoundedEvolution.norm_evol_apply
import Definitions.Def_ChapterEnergyBandDecomposition
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
open BookProof.ChapterEnergyBoundedEvolution



open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

theorem BookProof.ChapterEnergyBoundedEvolution.norm_evol_apply (t : ℝ) (f : X → ℂ) (x : X) : ‖evol E t f x‖ = ‖f x‖ := by sorry
