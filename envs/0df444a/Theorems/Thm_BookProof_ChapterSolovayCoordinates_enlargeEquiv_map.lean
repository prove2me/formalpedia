-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayCoordinates_enlargeEquiv_map
-- name    : BookProof.ChapterSolovayCoordinates.enlargeEquiv_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:53:06.575166+00:00
-- url     : https://prove2.me/theorems/1a9a7a8e-a030-4617-895f-f363e23be8bb
-- title:
--   `BookProof.ChapterSolovayCoordinates.enlargeEquiv_map` (N k : ℕ) (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist] : Measure.map (enlargeEquiv N k) (coordinateStateM
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayCoordinates`.
--
--   `BookProof.ChapterSolovayCoordinates.enlargeEquiv_map` (N k : ℕ) (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist] : Measure.map (enlargeEquiv N k) (coordinateStateMeasure N headDist) = coordinateStateMeasure (N + k) (enlargedHeadMeasure N k headDist)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayCoordinates.enlargeEquiv_map`.

-- Generated from ChapterSolovayCoordinates.lean — theorem BookProof.ChapterSolovayCoordinates.enlargeEquiv_map
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates


open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem BookProof.ChapterSolovayCoordinates.enlargeEquiv_map (N k : ℕ) (headDist : Measure (Fin N → ℝ))
    [IsProbabilityMeasure headDist] :
    Measure.map (enlargeEquiv N k) (coordinateStateMeasure N headDist) =
      coordinateStateMeasure (N + k) (enlargedHeadMeasure N k headDist) := by sorry
