-- Prove2me | Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_eLpNorm_evol_sub_self_le
-- name    : BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:46:52.537888+00:00
-- url     : https://prove2.me/theorems/7e2a292c-4d6e-4835-bfc0-d78f6cd02a49
-- title:
--   `BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le` {Emax : ℝ} (h : EnergyLimited E μ Emax f) (t : ℝ) : eLpNorm (evol E t f - f) 2 μ ≤ ENNReal.ofReal (|t| * Emax) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBoundedEvolution`.
--
--   `BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le` {Emax : ℝ} (h : EnergyLimited E μ Emax f) (t : ℝ) : eLpNorm (evol E t f - f) 2 μ ≤ ENNReal.ofReal (|t| * Emax) * eLpNorm f 2 μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le`.

-- Generated from ChapterEnergyBoundedEvolution.lean — theorem BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le
import Definitions.Def_ChapterEnergyBandDecomposition
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
open BookProof.ChapterEnergyBoundedEvolution



open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

theorem BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_self_le {Emax : ℝ} (h : EnergyLimited E μ Emax f) (t : ℝ) :
    eLpNorm (evol E t f - f) 2 μ ≤ ENNReal.ofReal (|t| * Emax) * eLpNorm f 2 μ := by sorry
