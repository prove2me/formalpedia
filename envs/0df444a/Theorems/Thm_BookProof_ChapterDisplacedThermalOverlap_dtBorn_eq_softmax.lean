-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_dtBorn_eq_softmax
-- name    : BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:06:40.048189+00:00
-- url     : https://prove2.me/theorems/4c4335d6-0156-4858-b867-82f67bea89b2
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax` {m : ℕ} (nbar : ℝ≥0) (q : ℝ) (k : Fin m → ℝ) (j : Fin m) : dtBorn nbar q k j = BookProof.ChapterSoftmaxSharpness.scoreS
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax` {m : ℕ} (nbar : ℝ≥0) (q : ℝ) (k : Fin m → ℝ) (j : Fin m) : dtBorn nbar q k j = BookProof.ChapterSoftmaxSharpness.scoreSoftmax (inverseTemperature nbar) (fun l => -(q - k l) ^ 2) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.dtBorn_eq_softmax {m : ℕ} (nbar : ℝ≥0) (q : ℝ) (k : Fin m → ℝ) (j : Fin m) :
    dtBorn nbar q k j
      = BookProof.ChapterSoftmaxSharpness.scoreSoftmax (inverseTemperature nbar)
          (fun l => -(q - k l) ^ 2) j := by sorry
