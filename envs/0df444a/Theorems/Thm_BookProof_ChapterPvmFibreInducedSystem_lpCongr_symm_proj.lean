-- Prove2me | Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_lpCongr_symm_proj
-- name    : BookProof.ChapterPvmFibreInducedSystem.lpCongr_symm_proj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:50:00.979723+00:00
-- url     : https://prove2.me/theorems/b9c615fe-f4f2-46fb-bfd4-12983f521fbd
-- title:
--   `BookProof.ChapterPvmFibreInducedSystem.lpCongr_symm_proj` {μ ν : Measure X} (h : μ = ν) {E : Set X} (hE : MeasurableSet E) (f : Lp ℂ 2 ν) : (lpCongr h).symm (proj ν hE f) = proj μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmFibreInducedSystem`.
--
--   `BookProof.ChapterPvmFibreInducedSystem.lpCongr_symm_proj` {μ ν : Measure X} (h : μ = ν) {E : Set X} (hE : MeasurableSet E) (f : Lp ℂ 2 ν) : (lpCongr h).symm (proj ν hE f) = proj μ hE ((lpCongr h).symm f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmFibreInducedSystem.lpCongr_symm_proj`.

-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.lpCongr_symm_proj
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterL2FibreSum
import Definitions.Def_ChapterHilbertSumIntertwine
import Mathlib
import Definitions.Def_ChapterPvmFibreInducedSystem
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterPvmFibreInducedSystem


open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterPvmFibreInducedSystem.lpCongr_symm_proj {μ ν : Measure X} (h : μ = ν) {E : Set X} (hE : MeasurableSet E)
    (f : Lp ℂ 2 ν) :
    (lpCongr h).symm (proj ν hE f) = proj μ hE ((lpCongr h).symm f) := by sorry
