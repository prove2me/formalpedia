-- Prove2me | Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_gaussianPDFReal_mul_gaussianPDFReal
-- name    : BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:02:30.674998+00:00
-- url     : https://prove2.me/theorems/69af7b2b-1abe-46aa-a6ec-a2a903793cb6
-- title:
--   `BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal` (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : gaussianPDFReal a v x * gaussianPDFReal b v x = (Real.exp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDisplacedThermalOverlap`.
--
--   `BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal` (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : gaussianPDFReal a v x * gaussianPDFReal b v x = (Real.exp (-(a - b) ^ 2 / (4 * (v : ℝ))) / Real.sqrt (4 * π * v)) * gaussianPDFReal ((a + b) / 2) (v / 2) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal`.

-- Generated from ChapterDisplacedThermalOverlap.lean — theorem BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap


noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem BookProof.ChapterDisplacedThermalOverlap.gaussianPDFReal_mul_gaussianPDFReal (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal a v x * gaussianPDFReal b v x
      = (Real.exp (-(a - b) ^ 2 / (4 * (v : ℝ))) / Real.sqrt (4 * π * v))
        * gaussianPDFReal ((a + b) / 2) (v / 2) x := by sorry
