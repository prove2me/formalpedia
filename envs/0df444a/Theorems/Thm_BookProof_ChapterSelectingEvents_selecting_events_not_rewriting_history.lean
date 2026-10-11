-- Prove2me | Theorems.Thm_BookProof_ChapterSelectingEvents_selecting_events_not_rewriting_history
-- name    : BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:20:56.446157+00:00
-- url     : https://prove2.me/theorems/0500d80f-c69b-413b-8230-abfa08b32770
-- title:
--   `BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history` {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NullSingl
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSelectingEvents`.
--
--   `BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history` {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ] (E F : Set α) (_hE : MeasurableSet E) (hF : MeasurableSet F) (_hEpos : μ E > 0) (_hFpos : μ F > 0) : μ[F | E] = μ (E ∩ F) / μ E
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history`.

-- Generated from ChapterSelectingEvents.lean — theorem BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history
import Mathlib
import Definitions.Def_ChapterSelectingEvents
open BookProof.ChapterSelectingEvents


open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω Data : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {Seed Model : Type*} [Fintype Seed] [Fintype Model] [DecidableEq Model]

theorem BookProof.ChapterSelectingEvents.selecting_events_not_rewriting_history
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (E F : Set α) (_hE : MeasurableSet E) (hF : MeasurableSet F)
    (_hEpos : μ E > 0) (_hFpos : μ F > 0) :
    μ[F | E] = μ (E ∩ F) / μ E := by sorry
