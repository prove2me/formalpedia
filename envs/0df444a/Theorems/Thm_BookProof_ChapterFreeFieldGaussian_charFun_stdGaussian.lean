-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldGaussian_charFun_stdGaussian
-- name    : BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T04:20:16.914869+00:00
-- url     : https://prove2.me/theorems/c9685911-f61e-4871-8a8c-887a8b0251a4
-- title:
--   `BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian` (t : EuclideanSpace ℝ (Fin n)) : charFun (stdGaussian n) t = Complex.exp (-‖t‖ ^ 2 / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldGaussian`.
--
--   `BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian` (t : EuclideanSpace ℝ (Fin n)) : charFun (stdGaussian n) t = Complex.exp (-‖t‖ ^ 2 / 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian`.

-- Generated from ChapterFreeFieldGaussian.lean — theorem BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian
import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian
open BookProof.ChapterFreeFieldGaussian

variable {n : ℕ}


open MeasureTheory ProbabilityTheory Complex WithLp
open scoped RealInnerProductSpace ENNReal

theorem BookProof.ChapterFreeFieldGaussian.charFun_stdGaussian (t : EuclideanSpace ℝ (Fin n)) :
    charFun (stdGaussian n) t = Complex.exp (-‖t‖ ^ 2 / 2) := by sorry
