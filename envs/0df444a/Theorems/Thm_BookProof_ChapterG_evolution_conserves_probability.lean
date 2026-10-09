-- Prove2me | Theorems.Thm_BookProof_ChapterG_evolution_conserves_probability
-- name    : BookProof.ChapterG.evolution_conserves_probability
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:27:10.982446+00:00
-- url     : https://prove2.me/theorems/c88bc741-395f-4650-b8d6-3ee5bb603b09
-- title:
--   `BookProof.ChapterG.evolution_conserves_probability` {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) : IsProbabilityMeasure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.evolution_conserves_probability` {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) : IsProbabilityMeasure (μ.map T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.evolution_conserves_probability`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.evolution_conserves_probability
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]
variable {A : Type*} [Ring A]

theorem BookProof.ChapterG.evolution_conserves_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) :
    IsProbabilityMeasure (μ.map T) := by sorry
