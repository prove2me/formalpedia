-- Prove2me | Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_homEmb_proj
-- name    : BookProof.ChapterPvmFibreInducedSystem.homEmb_proj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:50:08.662751+00:00
-- url     : https://prove2.me/theorems/2a930c14-5704-4574-aa04-0b0f3c1a924c
-- title:
--   `BookProof.ChapterPvmFibreInducedSystem.homEmb_proj` (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) {E : Set X} (hE : MeasurableSet E) (f : Lp ℂ 2 μ) : homEmb hmu ψ (proj μ hE f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmFibreInducedSystem`.
--
--   `BookProof.ChapterPvmFibreInducedSystem.homEmb_proj` (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) {E : Set X} (hE : MeasurableSet E) (f : Lp ℂ 2 μ) : homEmb hmu ψ (proj μ hE f) = P.p E (homEmb hmu ψ f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmFibreInducedSystem.homEmb_proj`.

-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.homEmb_proj
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

variable {P : Pvm X H} {S : Set H} {μ : Measure X}

theorem BookProof.ChapterPvmFibreInducedSystem.homEmb_proj (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) (ψ : S) {E : Set X}
    (hE : MeasurableSet E) (f : Lp ℂ 2 μ) :
    homEmb hmu ψ (proj μ hE f) = P.p E (homEmb hmu ψ f) := by sorry
