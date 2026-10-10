-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtOverlap_eq
-- name    : BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:50.988964+00:00
-- url     : https://prove2.me/theorems/26d7a32f-e617-4e22-8a52-3d97ef42e00a
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq` (nbar : ℝ≥0) (a b : ℝ) : dtOverlap nbar a b = Real.exp (-(a - b) ^ 2 / (4 * ((nbar : ℝ) + 1 / 2))) / Real.sqrt (4 * π * ((nb
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq` (nbar : ℝ≥0) (a b : ℝ) : dtOverlap nbar a b = Real.exp (-(a - b) ^ 2 / (4 * ((nbar : ℝ) + 1 / 2))) / Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.dtOverlap_eq (nbar : ℝ≥0) (a b : ℝ) :
    dtOverlap nbar a b
      = Real.exp (-(a - b) ^ 2 / (4 * ((nbar : ℝ) + 1 / 2)))
        / Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2)) := by sorry
