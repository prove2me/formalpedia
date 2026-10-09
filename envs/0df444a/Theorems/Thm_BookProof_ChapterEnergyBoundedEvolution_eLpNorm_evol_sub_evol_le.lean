-- Prove2me | Theorems.Thm_BookProof_ChapterEnergyBoundedEvolution_eLpNorm_evol_sub_evol_le
-- name    : BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:46:44.60535+00:00
-- url     : https://prove2.me/theorems/5c3e974e-6d26-40d1-8bf6-9496f5614ac5
-- title:
--   `BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le` {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) : eLpNorm (evol E t f - evol E s f) 2 μ ≤ ENNReal.ofReal (|t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBoundedEvolution`.
--
--   `BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le` {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) : eLpNorm (evol E t f - evol E s f) 2 μ ≤ ENNReal.ofReal (|t - s| * Emax) * eLpNorm f 2 μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le`.

-- Generated from ChapterEnergyBoundedEvolution.lean — theorem BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le
import Definitions.Def_ChapterEnergyBandDecomposition
import Mathlib
import Definitions.Def_ChapterEnergyBoundedEvolution
open BookProof.ChapterEnergyBoundedEvolution



open MeasureTheory Complex
open scoped ENNReal
open BookProof.EnergyBandDecomposition

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : X → ℝ} {f : X → ℂ}

theorem BookProof.ChapterEnergyBoundedEvolution.eLpNorm_evol_sub_evol_le {Emax : ℝ} (h : EnergyLimited E μ Emax f) (s t : ℝ) :
    eLpNorm (evol E t f - evol E s f) 2 μ
      ≤ ENNReal.ofReal (|t - s| * Emax) * eLpNorm f 2 μ := by sorry
