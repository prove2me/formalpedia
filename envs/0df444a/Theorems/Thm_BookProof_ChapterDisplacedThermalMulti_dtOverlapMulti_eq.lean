-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtOverlapMulti_eq
-- name    : BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:01:27.322299+00:00
-- url     : https://prove2.me/theorems/7316bced-6997-478e-a3f1-feeb79234911
-- title:
--   `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq` (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) : dtOverlapMulti nbar a b = Real.exp (-‖a - b‖ ^ 2 / (4 * ((nbar : ℝ) + 1 /
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalMulti`.
--
--   `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq` (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) : dtOverlapMulti nbar a b = Real.exp (-‖a - b‖ ^ 2 / (4 * ((nbar : ℝ) + 1 / 2))) / (Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2))) ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq`.

-- Generated from ChapterDisplacedThermalMulti.lean — theorem BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ChapterDisplacedThermalOverlap
open BookProof.HermiteProductCore
open BookProof.ChapterDisplacedThermalMulti


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

theorem BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) :
    dtOverlapMulti nbar a b
      = Real.exp (-‖a - b‖ ^ 2 / (4 * ((nbar : ℝ) + 1 / 2)))
        / (Real.sqrt (4 * π * ((nbar : ℝ) + 1 / 2))) ^ n := by sorry
