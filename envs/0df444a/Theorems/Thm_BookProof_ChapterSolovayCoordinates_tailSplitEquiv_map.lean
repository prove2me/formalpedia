-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayCoordinates_tailSplitEquiv_map
-- name    : BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T15:53:06.073063+00:00
-- url     : https://prove2.me/theorems/d5e520ab-9082-47da-8dd6-019e672114b2
-- title:
--   `BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map` (k : ℕ) : Measure.map (tailSplitEquiv k) coordinateTailMeasure = (gaussianHead k).prod coordinateTailMeasure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayCoordinates`.
--
--   `BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map` (k : ℕ) : Measure.map (tailSplitEquiv k) coordinateTailMeasure = (gaussianHead k).prod coordinateTailMeasure
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map`.

-- Generated from ChapterSolovayCoordinates.lean — theorem BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map
import Mathlib
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovayCoordinates


open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

theorem BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map (k : ℕ) :
    Measure.map (tailSplitEquiv k) coordinateTailMeasure =
      (gaussianHead k).prod coordinateTailMeasure := by sorry
