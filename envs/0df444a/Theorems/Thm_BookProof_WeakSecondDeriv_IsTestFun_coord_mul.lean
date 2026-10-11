-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_coord_mul
-- name    : BookProof.WeakSecondDeriv.IsTestFun.coord_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:09:46.7128+00:00
-- url     : https://prove2.me/theorems/f4ba4944-7198-427b-885d-34af64d0e068
-- title:
--   `BookProof.WeakSecondDeriv.IsTestFun.coord_mul` {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (fun x => x * g x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.IsTestFun.coord_mul` {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (fun x => x * g x)
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.IsTestFun.coord_mul`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.IsTestFun.coord_mul
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.IsTestFun.coord_mul {g : ℝ → ℝ} (h : IsTestFun g) : IsTestFun (fun x => x * g x) := by sorry
