-- Prove2me | Theorems.Thm_BookProof_ChapterProbabilityInterface_translated_event_probability
-- name    : BookProof.ChapterProbabilityInterface.translated_event_probability
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:15:34.934915+00:00
-- url     : https://prove2.me/theorems/25be3eee-d623-4fda-b5b2-3d53b6787d02
-- title:
--   `BookProof.ChapterProbabilityInterface.translated_event_probability` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) (s : Set Y) (hs : Measurable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityInterface`.
--
--   `BookProof.ChapterProbabilityInterface.translated_event_probability` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) (s : Set Y) (hs : MeasurableSet s) : transportMeasure e μ s = μ (e ⁻¹' s)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterProbabilityInterface.translated_event_probability`.

-- Generated from ChapterProbabilityInterface.lean — theorem BookProof.ChapterProbabilityInterface.translated_event_probability
import Mathlib
import Definitions.Def_ChapterProbabilityInterface
open BookProof.ChapterProbabilityInterface


open MeasureTheory

theorem BookProof.ChapterProbabilityInterface.translated_event_probability {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X)
    (s : Set Y) (hs : MeasurableSet s) :
    transportMeasure e μ s = μ (e ⁻¹' s) := by sorry
