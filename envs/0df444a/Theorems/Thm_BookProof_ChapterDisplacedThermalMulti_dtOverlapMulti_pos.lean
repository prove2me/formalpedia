-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtOverlapMulti_pos
-- name    : BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:01:19.013008+00:00
-- url     : https://prove2.me/theorems/d8522281-5f5c-4798-a3f6-4be6d7049b75
-- title:
--   `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos` (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) : 0 < dtOverlapMulti nbar a b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalMulti`.
--
--   `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos` (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) : 0 < dtOverlapMulti nbar a b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos`.

-- Generated from ChapterDisplacedThermalMulti.lean — theorem BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalMulti


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

theorem BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_pos (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) :
    0 < dtOverlapMulti nbar a b := by sorry
