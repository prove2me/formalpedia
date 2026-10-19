-- Prove2me | Theorems.Thm_BookProof_ChapterPvmScalarMeasure_quasiInvariant_of_null_iff
-- name    : BookProof.ChapterPvmScalarMeasure.quasiInvariant_of_null_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T20:55:43.596451+00:00
-- url     : https://prove2.me/theorems/e02c9205-a405-4a6b-9bcd-894af004475b
-- title:
--   `BookProof.ChapterPvmScalarMeasure.quasiInvariant_of_null_iff` [CompleteSpace H] (T : ContinuousImprimitivitySystem G X H) {μ : Measure X} (hnull : ∀ E : Set X, MeasurableSet E → (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmScalarMeasure`.
--
--   `BookProof.ChapterPvmScalarMeasure.quasiInvariant_of_null_iff` [CompleteSpace H] (T : ContinuousImprimitivitySystem G X H) {μ : Measure X} (hnull : ∀ E : Set X, MeasurableSet E → (μ E = 0 ↔ T.P.p E = 0)) : QuasiInvariant μ G
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmScalarMeasure.quasiInvariant_of_null_iff`.

-- Generated from ChapterPvmScalarMeasure.lean — theorem BookProof.ChapterPvmScalarMeasure.quasiInvariant_of_null_iff
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

theorem BookProof.ChapterPvmScalarMeasure.quasiInvariant_of_null_iff [CompleteSpace H] (T : ContinuousImprimitivitySystem G X H)
    {μ : Measure X} (hnull : ∀ E : Set X, MeasurableSet E → (μ E = 0 ↔ T.P.p E = 0)) :
    QuasiInvariant μ G := by sorry
