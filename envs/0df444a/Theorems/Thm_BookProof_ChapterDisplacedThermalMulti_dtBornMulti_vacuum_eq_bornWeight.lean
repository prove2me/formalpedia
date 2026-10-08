-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtBornMulti_vacuum_eq_bornWeight
-- name    : BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:22.329859+00:00
-- url     : https://prove2.me/theorems/85dfebbe-d83a-4e91-aa7c-c334f809a18c
-- title:
--   `BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : dtBornMulti 0 (Real.sq
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalMulti`.
--
--   `BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : dtBornMulti 0 (Real.sqrt 2 • q) (fun l => Real.sqrt 2 • k l) j = BookProof.ChapterSoftmaxBorn.bornWeight q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight`.

-- Generated from ChapterDisplacedThermalMulti.lean — theorem BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalOverlap
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalMulti


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

theorem BookProof.ChapterDisplacedThermalMulti.dtBornMulti_vacuum_eq_bornWeight (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    dtBornMulti 0 (Real.sqrt 2 • q) (fun l => Real.sqrt 2 • k l) j
      = BookProof.ChapterSoftmaxBorn.bornWeight q k j := by sorry
