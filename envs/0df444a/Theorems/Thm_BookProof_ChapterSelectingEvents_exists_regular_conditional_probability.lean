-- Prove2me | Theorems.Thm_BookProof_ChapterSelectingEvents_exists_regular_conditional_probability
-- name    : BookProof.ChapterSelectingEvents.exists_regular_conditional_probability
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:45:27.578623+00:00
-- url     : https://prove2.me/theorems/68f7a7c0-e57e-4d42-b85b-b13f6de757b5
-- title:
--   `BookProof.ChapterSelectingEvents.exists_regular_conditional_probability` [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace Data] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Da
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSelectingEvents`.
--
--   `BookProof.ChapterSelectingEvents.exists_regular_conditional_probability` [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace Data] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Data) : ∃ κ : Kernel Data Ω, IsMarkovKernel κ ∧ (μ.map X) ⊗ₘ κ = μ.map (fun ω => (X ω, ω))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSelectingEvents.exists_regular_conditional_probability`.

-- Generated from ChapterSelectingEvents.lean — theorem BookProof.ChapterSelectingEvents.exists_regular_conditional_probability
import Mathlib
import Definitions.Def_ChapterSelectingEvents
open BookProof.ChapterSelectingEvents


open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {Ω Data : Type*} [MeasurableSpace Ω]

theorem BookProof.ChapterSelectingEvents.exists_regular_conditional_probability
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace Data]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → Data) :
    ∃ κ : Kernel Data Ω, IsMarkovKernel κ ∧
      (μ.map X) ⊗ₘ κ = μ.map (fun ω => (X ω, ω)) := by sorry
