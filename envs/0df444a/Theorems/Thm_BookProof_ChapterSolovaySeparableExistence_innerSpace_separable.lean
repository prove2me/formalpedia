-- Prove2me | Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_innerSpace_separable
-- name    : BookProof.ChapterSolovaySeparableExistence.innerSpace_separable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:45:53.916784+00:00
-- url     : https://prove2.me/theorems/f528a29b-9911-42cf-bcde-d3b303fe53df
-- title:
--   `BookProof.ChapterSolovaySeparableExistence.innerSpace_separable` (N : ℕ) : TopologicalSpace.SeparableSpace (_root_.InnerSpace N)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovaySeparableExistence`.
--
--   `BookProof.ChapterSolovaySeparableExistence.innerSpace_separable` (N : ℕ) : TopologicalSpace.SeparableSpace (_root_.InnerSpace N)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovaySeparableExistence.innerSpace_separable`.

-- Generated from ChapterSolovaySeparableExistence.lean — theorem BookProof.ChapterSolovaySeparableExistence.innerSpace_separable
import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Definitions.Def_PhysMeasureBasis
open PhysMeasureBasis


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

theorem BookProof.ChapterSolovaySeparableExistence.innerSpace_separable (N : ℕ) :
    TopologicalSpace.SeparableSpace (_root_.InnerSpace N) := by sorry
