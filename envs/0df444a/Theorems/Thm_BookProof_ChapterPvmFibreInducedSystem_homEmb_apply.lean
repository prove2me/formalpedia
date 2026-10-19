-- Prove2me | Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_homEmb_apply
-- name    : BookProof.ChapterPvmFibreInducedSystem.homEmb_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:49:18.081984+00:00
-- url     : https://prove2.me/theorems/dbd630c6-d7c4-4b7f-a843-dc52087ba1fa
-- title:
--   `BookProof.ChapterPvmFibreInducedSystem.homEmb_apply` (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) (f : Lp ℂ 2 μ) : homEmb hmu ψ f = swIsom P (ψ : H) ((lpCongr (hmu ψ)).symm f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmFibreInducedSystem`.
--
--   `BookProof.ChapterPvmFibreInducedSystem.homEmb_apply` (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) (f : Lp ℂ 2 μ) : homEmb hmu ψ f = swIsom P (ψ : H) ((lpCongr (hmu ψ)).symm f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmFibreInducedSystem.homEmb_apply`.

-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.homEmb_apply
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

theorem BookProof.ChapterPvmFibreInducedSystem.homEmb_apply (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) (f : Lp ℂ 2 μ) :
    homEmb hmu ψ f = swIsom P (ψ : H) ((lpCongr (hmu ψ)).symm f) := by sorry
