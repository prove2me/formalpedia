-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_integral_eq_neg_integral_coord_mul_deriv
-- name    : BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:12.391504+00:00
-- url     : https://prove2.me/theorems/e6087d80-dff4-44ac-a286-86180efa7da5
-- title:
--   `BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv` {g : ℝ → ℝ} (h : IsTestFun g) : ∫ x, g x = -∫ x, x * deriv g x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv` {g : ℝ → ℝ} (h : IsTestFun g) : ∫ x, g x = -∫ x, x * deriv g x
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.integral_eq_neg_integral_coord_mul_deriv {g : ℝ → ℝ} (h : IsTestFun g) :
    ∫ x, g x = -∫ x, x * deriv g x := by sorry
