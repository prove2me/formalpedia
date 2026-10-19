-- Prove2me | Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_pvm_induced_system_homogeneous
-- name    : BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:50:28.297992+00:00
-- url     : https://prove2.me/theorems/22bbc917-7103-4281-ae78-71159e6c975b
-- title:
--   `BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous` [Countable S] (hS : OrthCyclicFamily P S) (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmFibreInducedSystem`.
--
--   `BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous` [Countable S] (hS : OrthCyclicFamily P S) (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H)) (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) : ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre S) 2 μ, ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous`.

-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous
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

theorem BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous [Countable S] (hS : OrthCyclicFamily P S)
    (hdense : Dense ((Submodule.span ℂ (familyOrbit P S) : Submodule ℂ H) : Set H))
    (hmu : ∀ ψ : S, pvmMeasure P (ψ : H) = μ) :
    ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre S) 2 μ,
      ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v) := by sorry
