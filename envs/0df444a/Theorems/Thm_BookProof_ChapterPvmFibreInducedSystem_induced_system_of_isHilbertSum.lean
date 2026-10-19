-- Prove2me | Theorems.Thm_BookProof_ChapterPvmFibreInducedSystem_induced_system_of_isHilbertSum
-- name    : BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:49:09.859729+00:00
-- url     : https://prove2.me/theorems/dba2f803-d6b5-4020-b96b-cb71ce22ece6
-- title:
--   `BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum` {ι : Type*} [Countable ι] (P : Pvm X H) (μ : Measure X) (V : ∀ _ : ι, Lp ℂ 2 μ →ₗᵢ[ℂ] H) (hsum : IsHilbertSu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmFibreInducedSystem`.
--
--   `BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum` {ι : Type*} [Countable ι] (P : Pvm X H) (μ : Measure X) (V : ∀ _ : ι, Lp ℂ 2 μ →ₗᵢ[ℂ] H) (hsum : IsHilbertSum ℂ (fun _ : ι => Lp ℂ 2 μ) V) (hint : ∀ (i : ι) (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 μ), V i (proj μ hE f) = P.p E (V i f)) : ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre ι) 2 μ, ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum`.

-- Generated from ChapterPvmFibreInducedSystem.lean — theorem BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum
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

theorem BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum {ι : Type*} [Countable ι]
    (P : Pvm X H) (μ : Measure X) (V : ∀ _ : ι, Lp ℂ 2 μ →ₗᵢ[ℂ] H)
    (hsum : IsHilbertSum ℂ (fun _ : ι => Lp ℂ 2 μ) V)
    (hint : ∀ (i : ι) (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 μ),
      V i (proj μ hE f) = P.p E (V i f)) :
    ∃ W : H ≃ₗᵢ[ℂ] Lp (Fibre ι) 2 μ,
      ∀ (E : Set X) (hE : MeasurableSet E) (v : H), W (P.p E v) = proj μ hE (W v) := by sorry
