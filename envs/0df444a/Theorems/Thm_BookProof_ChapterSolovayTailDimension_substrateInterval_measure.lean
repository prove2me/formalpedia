-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrateInterval_measure
-- name    : BookProof.ChapterSolovayTailDimension.substrateInterval_measure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T12:22:14.570741+00:00
-- url     : https://prove2.me/theorems/aa2884bb-6492-4128-94b9-93d2fed8d809
-- title:
--   `BookProof.ChapterSolovayTailDimension.substrateInterval_measure` (n : ℕ) : unitMeasure (substrateInterval n) = ENNReal.ofReal (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayTailDimension`.
--
--   `BookProof.ChapterSolovayTailDimension.substrateInterval_measure` (n : ℕ) : unitMeasure (substrateInterval n) = ENNReal.ofReal (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayTailDimension.substrateInterval_measure`.

-- Generated from ChapterSolovayTailDimension.lean — theorem BookProof.ChapterSolovayTailDimension.substrateInterval_measure
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Definitions.Def_PhysMeasureBasis
open PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension


noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal

theorem BookProof.ChapterSolovayTailDimension.substrateInterval_measure (n : ℕ) :
    unitMeasure (substrateInterval n)
      = ENNReal.ofReal (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by sorry
