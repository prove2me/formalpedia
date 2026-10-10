-- Prove2me | Theorems.Thm_BookProof_ChapterProbabilityInterface_transportMeasure_isProbability
-- name    : BookProof.ChapterProbabilityInterface.transportMeasure_isProbability
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:16:32.358979+00:00
-- url     : https://prove2.me/theorems/d4ce1594-a43f-4770-aa77-998ec3916290
-- title:
--   `BookProof.ChapterProbabilityInterface.transportMeasure_isProbability` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) [IsProbabilityMeasure μ] :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityInterface`.
--
--   `BookProof.ChapterProbabilityInterface.transportMeasure_isProbability` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) [IsProbabilityMeasure μ] : IsProbabilityMeasure (transportMeasure e μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterProbabilityInterface.transportMeasure_isProbability`.

-- Generated from ChapterProbabilityInterface.lean — theorem BookProof.ChapterProbabilityInterface.transportMeasure_isProbability
import Mathlib
import Definitions.Def_ChapterProbabilityInterface
open BookProof.ChapterProbabilityInterface


open MeasureTheory

theorem BookProof.ChapterProbabilityInterface.transportMeasure_isProbability {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (transportMeasure e μ) := by sorry
