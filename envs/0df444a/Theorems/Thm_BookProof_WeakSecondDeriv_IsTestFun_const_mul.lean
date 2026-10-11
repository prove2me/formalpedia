-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_const_mul
-- name    : BookProof.WeakSecondDeriv.IsTestFun.const_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:09:43.185791+00:00
-- url     : https://prove2.me/theorems/deabfaa2-d939-474a-97eb-c78b883df9a6
-- title:
--   `BookProof.WeakSecondDeriv.IsTestFun.const_mul` {g : ℝ → ℝ} (h : IsTestFun g) (a : ℝ) : IsTestFun (fun x => a * g x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.IsTestFun.const_mul` {g : ℝ → ℝ} (h : IsTestFun g) (a : ℝ) : IsTestFun (fun x => a * g x)
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.IsTestFun.const_mul`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.IsTestFun.const_mul
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.IsTestFun.const_mul {g : ℝ → ℝ} (h : IsTestFun g) (a : ℝ) : IsTestFun (fun x => a * g x) := by sorry
