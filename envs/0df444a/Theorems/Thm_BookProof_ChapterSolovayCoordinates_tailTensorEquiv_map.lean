-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayCoordinates_tailTensorEquiv_map
-- name    : BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:44:32.130012+00:00
-- url     : https://prove2.me/theorems/7a99826c-0ab3-4872-b08a-91628e4c479b
-- title:
--   `BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map` : Measure.map tailTensorEquiv (coordinateTailMeasure.prod coordinateTailMeasure) = coordinateTailMeasure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayCoordinates`.
--
--   `BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map` : Measure.map tailTensorEquiv (coordinateTailMeasure.prod coordinateTailMeasure) = coordinateTailMeasure
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map`.

-- Generated from ChapterSolovayCoordinates.lean — theorem BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates


open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem BookProof.ChapterSolovayCoordinates.tailTensorEquiv_map :
    Measure.map tailTensorEquiv
      (coordinateTailMeasure.prod coordinateTailMeasure) = coordinateTailMeasure := by sorry
