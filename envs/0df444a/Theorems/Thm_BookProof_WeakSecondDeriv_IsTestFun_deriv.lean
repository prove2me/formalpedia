-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_deriv
-- name    : BookProof.WeakSecondDeriv.IsTestFun.deriv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:09:44.092622+00:00
-- url     : https://prove2.me/theorems/2ba6821c-f675-4e27-ad56-1cbe90e88e50
-- title:
--   `BookProof.WeakSecondDeriv.IsTestFun.deriv` {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (_root_.deriv g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.IsTestFun.deriv` {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (_root_.deriv g)
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.IsTestFun.deriv`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.IsTestFun.deriv
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.IsTestFun.deriv {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (_root_.deriv g) := by sorry
