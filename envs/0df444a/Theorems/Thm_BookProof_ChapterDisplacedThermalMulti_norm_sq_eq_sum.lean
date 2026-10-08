-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_norm_sq_eq_sum
-- name    : BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:00:56.312415+00:00
-- url     : https://prove2.me/theorems/b4181256-80fa-4e98-a31f-9895c874f67c
-- title:
--   `BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum` (a b : EuclideanSpace ℝ (Fin n)) : ‖a - b‖ ^ 2 = ∑ i, (a i - b i) ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalMulti`.
--
--   `BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum` (a b : EuclideanSpace ℝ (Fin n)) : ‖a - b‖ ^ 2 = ∑ i, (a i - b i) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum`.

-- Generated from ChapterDisplacedThermalMulti.lean — theorem BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum
import Definitions.Def_ChapterDisplacedThermalOverlap
import Mathlib
import Definitions.Def_ChapterDisplacedThermalMulti
open BookProof.ChapterDisplacedThermalMulti


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal


open BookProof.ChapterDisplacedThermalOverlap

variable {n m : ℕ}

theorem BookProof.ChapterDisplacedThermalMulti.norm_sq_eq_sum (a b : EuclideanSpace ℝ (Fin n)) :
    ‖a - b‖ ^ 2 = ∑ i, (a i - b i) ^ 2 := by sorry
