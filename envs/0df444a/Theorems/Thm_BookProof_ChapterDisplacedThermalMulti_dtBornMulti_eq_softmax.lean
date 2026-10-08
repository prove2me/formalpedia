-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtBornMulti_eq_softmax
-- name    : BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:07.332417+00:00
-- url     : https://prove2.me/theorems/3a077dc3-4cc0-4ec7-b2ba-d51b0b3e1aad
-- title:
--   `BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax` (nbar : ℝ≥0) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : dtBornMulti nbar q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalMulti`.
--
--   `BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax` (nbar : ℝ≥0) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : dtBornMulti nbar q k j = BookProof.ChapterSoftmaxSharpness.scoreSoftmax (inverseTemperature nbar) (fun l => -‖q - k l‖ ^ 2) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax`.

-- Generated from ChapterDisplacedThermalMulti.lean — theorem BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalOverlap
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalMulti


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

theorem BookProof.ChapterDisplacedThermalMulti.dtBornMulti_eq_softmax (nbar : ℝ≥0) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    dtBornMulti nbar q k j
      = BookProof.ChapterSoftmaxSharpness.scoreSoftmax (inverseTemperature nbar)
          (fun l => -‖q - k l‖ ^ 2) j := by sorry
