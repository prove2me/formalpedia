-- Prove2me | Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_separable_carrier_tail_infinite_dimensional
-- name    : BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T22:46:11.338612+00:00
-- url     : https://prove2.me/theorems/4c34f748-de2d-422f-903e-1d0e4c6919d2
-- title:
--   `BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional` : ¬ FiniteDimensional ℝ _root_.InnerTail
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovaySeparableExistence`.
--
--   `BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional` : ¬ FiniteDimensional ℝ _root_.InnerTail
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional`.

-- Generated from ChapterSolovaySeparableExistence.lean — theorem BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional
import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Definitions.Def_PhysMeasureBasis
open PhysMeasureBasis


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

theorem BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional :
    ¬ FiniteDimensional ℝ _root_.InnerTail := by sorry
