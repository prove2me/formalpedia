-- Prove2me | Theorems.Thm_BookProof_ChapterSolovayTailDimension_tail_infinite_dimensional
-- name    : BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-02T13:16:31.104779+00:00
-- url     : https://prove2.me/theorems/af12195f-baff-4b45-ad0f-2d960a6cf88d
-- title:
--   `BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional` : ¬ FiniteDimensional ℝ _root_.InnerTail
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovayTailDimension`.
--
--   `BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional` : ¬ FiniteDimensional ℝ _root_.InnerTail
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional`.

-- Generated from ChapterSolovayTailDimension.lean — theorem BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterSolovay
open PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension


noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal

theorem BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional : ¬ FiniteDimensional ℝ _root_.InnerTail := by sorry
