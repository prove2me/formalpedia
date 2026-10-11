-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_exists_supp
-- name    : BookProof.WeakSecondDeriv.exists_supp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:10:28.743295+00:00
-- url     : https://prove2.me/theorems/0b3a2214-8dd4-4d8f-a1cb-7842341311d0
-- title:
--   `BookProof.WeakSecondDeriv.exists_supp` {g : ℝ → ℝ} (h : IsTestFun g) : ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Icc (-R) R
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.exists_supp` {g : ℝ → ℝ} (h : IsTestFun g) : ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Icc (-R) R
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.exists_supp`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.exists_supp
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

theorem BookProof.WeakSecondDeriv.exists_supp {g : ℝ → ℝ} (h : IsTestFun g) :
    ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Icc (-R) R := by sorry
