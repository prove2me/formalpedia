-- Prove2me | Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_isHilbertSum_homEmb
-- name    : BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:50:05.085662+00:00
-- url     : https://prove2.me/theorems/a1da4ce8-cfd3-43de-a023-69303ff64f75
-- title:
--   `BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb` (hS : OrthCyclicFamily P S) (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H)) (hmu : ∀ ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmFibreInducedSystem`.
--
--   `BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb` (hS : OrthCyclicFamily P S) (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H)) (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) : IsHilbertSum ℂ (fun _ : S => Lp ℂ 2 μ) (homEmb hmu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb`.

-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicUnitary
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterPvmInducedSystem
import Definitions.Def_ChapterMackeyQuasiInvariant
import Definitions.Def_ChapterL2FibreSum
import Definitions.Def_ChapterHilbertSumIntertwine
import Mathlib
import Definitions.Def_ChapterPvmFibreInducedSystem
open BookProof.ChapterPvmFibreInducedSystem


open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicUnitary
open BookProof.ChapterPvmCyclicDecomposition BookProof.ChapterPvmInducedSystem
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterL2FibreSum
open BookProof.ChapterHilbertSumIntertwine

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {P : Pvm X H} {S : Set H} {μ : Measure X}

theorem BookProof.ChapterPvmFibreInducedSystem.isHilbertSum_homEmb (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) :
    IsHilbertSum ℂ (fun _ : S => Lp ℂ 2 μ) (homEmb hmu) := by sorry
