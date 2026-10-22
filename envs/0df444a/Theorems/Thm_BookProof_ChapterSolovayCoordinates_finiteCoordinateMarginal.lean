-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayCoordinates_finiteCoordinateMarginal
-- name    : BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:53:01.215017+00:00
-- url     : https://prove2.me/theorems/280626bd-1f75-4052-952f-371b6ad5cf24
-- title:
--   `BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal` (I : Finset ℕ) : Measure.map I.restrict coordinateTailMeasure = Measure.pi (fun _ : I => standardGaussian)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayCoordinates`.
--
--   `BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal` (I : Finset ℕ) : Measure.map I.restrict coordinateTailMeasure = Measure.pi (fun _ : I => standardGaussian)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal`.

-- Generated from ChapterSolovayCoordinates.lean — theorem BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates


open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem BookProof.ChapterSolovayCoordinates.finiteCoordinateMarginal (I : Finset ℕ) :
    Measure.map I.restrict coordinateTailMeasure =
      Measure.pi (fun _ : I => standardGaussian) := by sorry
