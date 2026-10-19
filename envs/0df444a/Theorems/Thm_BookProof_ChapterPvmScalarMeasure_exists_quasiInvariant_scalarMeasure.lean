-- Prove2me | Theorems.Thm_BookProof_ChapterPvmScalarMeasure_exists_quasiInvariant_scalarMeasure
-- name    : BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:55:59.411212+00:00
-- url     : https://prove2.me/theorems/9c20e8bd-3162-42aa-862f-46dcc4e161e2
-- title:
--   `BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure` [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) : ∃ μ : Meas
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmScalarMeasure`.
--
--   `BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure` [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) : ∃ μ : Measure X, IsFiniteMeasure μ ∧ QuasiInvariant μ G ∧ ∀ E : Set X, MeasurableSet E → (μ E = 0 ↔ T.P.p E = 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure`.

-- Generated from ChapterPvmScalarMeasure.lean — theorem BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure
import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterPvmCyclicDecomposition
import Definitions.Def_ChapterMackeyConverse
import Definitions.Def_ChapterPvmInducedSystem
import Mathlib
import Definitions.Def_ChapterPvmScalarMeasure
import Definitions.Def_ChapterMackeyQuasiInvariant
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

theorem BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (T : ContinuousImprimitivitySystem G X H) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ QuasiInvariant μ G ∧
      ∀ E : Set X, MeasurableSet E → (μ E = 0 ↔ T.P.p E = 0) := by sorry
