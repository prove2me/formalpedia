-- Prove2me | Theorems.Thm_BookProof_ChapterPvmScalarMeasure_exists_induced_system_in_measure_class
-- name    : BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:55:32.12724+00:00
-- url     : https://prove2.me/theorems/05111acd-b971-455b-a502-88b6104c9894
-- title:
--   `BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class` [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) : ∃ (μ :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmScalarMeasure`.
--
--   `BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class` [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) : ∃ (μ : Measure X) (S : Set H) (W : H ≃ₗᵢ[ℂ] lp (fun ψ : S => Lp ℂ 2 (pvmMeasure T.P (ψ : H))) 2), IsFiniteMeasure μ ∧ QuasiInvariant μ G ∧ S.Countable ∧ (∀ ψ ∈ S, ‖ψ‖ = 1) ∧ (∀ ψ : S, pvmMeasure T.P (ψ : H) ≪ μ) ∧ (∀ (E : Set X) (hE : MeasurableSet E) (v : H) (ψ : S), W (T.P.p E v) ψ = proj (pvmMeasure T.P (ψ : H)) hE (W v ψ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class`.

-- Generated from ChapterPvmScalarMeasure.lean — theorem BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterMackeyConverse
import Definitions.Def_ChapterPvmInducedSystem
import Mathlib
import Definitions.Def_ChapterPvmScalarMeasure
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterMackeyQuasiInvariant
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterMackeyQuasiInvariant
open BookProof.ChapterPvmScalarMeasure


open MeasureTheory
open scoped InnerProductSpace


open BookProof.ChapterPvmMeasure BookProof.ChapterPvmCyclicDecomposition
open BookProof.ChapterMackeyQuasiInvariant BookProof.ChapterMackeyConverse
open BookProof.ChapterPvmInducedSystem

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type*} [Group G] [MulAction G X]

theorem BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) :
    ∃ (μ : Measure X) (S : Set H)
      (W : H ≃ₗᵢ[ℂ] lp (fun ψ : S => Lp ℂ 2 (pvmMeasure T.P (ψ : H))) 2),
      IsFiniteMeasure μ ∧ QuasiInvariant μ G ∧ S.Countable ∧
      (∀ ψ ∈ S, ‖ψ‖ = 1) ∧
      (∀ ψ : S, pvmMeasure T.P (ψ : H) ≪ μ) ∧
      (∀ (E : Set X) (hE : MeasurableSet E) (v : H) (ψ : S),
        W (T.P.p E v) ψ = proj (pvmMeasure T.P (ψ : H)) hE (W v ψ)) := by sorry
