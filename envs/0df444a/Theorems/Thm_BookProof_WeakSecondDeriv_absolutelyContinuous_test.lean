-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_absolutelyContinuous_test
-- name    : BookProof.WeakSecondDeriv.absolutelyContinuous_test
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:35.554008+00:00
-- url     : https://prove2.me/theorems/a0180127-eeda-427e-b4c0-5385d504ffd6
-- title:
--   `BookProof.WeakSecondDeriv.absolutelyContinuous_test` {g : ℝ → ℝ} (hg : IsTestFun g) (a b : ℝ) : AbsolutelyContinuousOnInterval g a b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.absolutelyContinuous_test` {g : ℝ → ℝ} (hg : IsTestFun g) (a b : ℝ) : AbsolutelyContinuousOnInterval g a b
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.absolutelyContinuous_test`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.absolutelyContinuous_test
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem BookProof.WeakSecondDeriv.absolutelyContinuous_test {g : ℝ → ℝ} (hg : IsTestFun g) (a b : ℝ) :
    AbsolutelyContinuousOnInterval g a b := by sorry
