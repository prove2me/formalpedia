-- Prove2me | Theorems.Thm_BookProof_ChapterProbabilityInterface_transportMeasure_symm
-- name    : BookProof.ChapterProbabilityInterface.transportMeasure_symm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:14:57.055976+00:00
-- url     : https://prove2.me/theorems/969d6770-b584-4b79-aae0-cf64bb3dad3d
-- title:
--   `BookProof.ChapterProbabilityInterface.transportMeasure_symm` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) : transportMeasure e.symm (transpor
-- statement:
--   Prove the following Lean 4 theorem from `ChapterProbabilityInterface`.
--
--   `BookProof.ChapterProbabilityInterface.transportMeasure_symm` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) : transportMeasure e.symm (transportMeasure e μ) = μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterProbabilityInterface.transportMeasure_symm`.

-- Generated from ChapterProbabilityInterface.lean — theorem BookProof.ChapterProbabilityInterface.transportMeasure_symm
import Mathlib
import Definitions.Def_ChapterProbabilityInterface
open BookProof.ChapterProbabilityInterface


open MeasureTheory

theorem BookProof.ChapterProbabilityInterface.transportMeasure_symm {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) :
    transportMeasure e.symm (transportMeasure e μ) = μ := by sorry
