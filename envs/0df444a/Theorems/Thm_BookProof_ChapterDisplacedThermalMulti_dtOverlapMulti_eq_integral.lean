-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalMulti_dtOverlapMulti_eq_integral
-- name    : BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:01:04.455489+00:00
-- url     : https://prove2.me/theorems/5d5b8c7d-f467-4266-9a60-482859a2f553
-- title:
--   `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral` (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) : dtOverlapMulti nbar a b = ∫ x : Fin n → ℝ, ∏ i, (gaussianPDFReal
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalMulti`.
--
--   `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral` (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) : dtOverlapMulti nbar a b = ∫ x : Fin n → ℝ, ∏ i, (gaussianPDFReal (a i) (tauNN nbar) (x i) * gaussianPDFReal (b i) (tauNN nbar) (x i))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral`.

-- Generated from ChapterDisplacedThermalMulti.lean — theorem BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral
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

theorem BookProof.ChapterDisplacedThermalMulti.dtOverlapMulti_eq_integral (nbar : ℝ≥0) (a b : EuclideanSpace ℝ (Fin n)) :
    dtOverlapMulti nbar a b
      = ∫ x : Fin n → ℝ, ∏ i, (gaussianPDFReal (a i) (tauNN nbar) (x i)
          * gaussianPDFReal (b i) (tauNN nbar) (x i)) := by sorry
