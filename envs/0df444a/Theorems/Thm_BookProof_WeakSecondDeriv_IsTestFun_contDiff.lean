-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
-- name    : BookProof.WeakSecondDeriv.IsTestFun.contDiff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:26.019286+00:00
-- url     : https://prove2.me/theorems/cfc619a4-a8de-403e-892f-faaad3edeb85
-- title:
--   `BookProof.WeakSecondDeriv.IsTestFun.contDiff` {g : ℝ → ℝ} (h : IsTestFun g) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.IsTestFun.contDiff` {g : ℝ → ℝ} (h : IsTestFun g) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.IsTestFun.contDiff`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.IsTestFun.contDiff
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.IsTestFun.contDiff {g : ℝ → ℝ} (h : IsTestFun g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by sorry
