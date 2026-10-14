-- Prove2me | Theorems.Thm_BookProof_WeylHamiltonian_smul_nonneg_isPositive
-- name    : BookProof.WeylHamiltonian.smul_nonneg_isPositive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:40:00.931445+00:00
-- url     : https://prove2.me/theorems/31626aa6-58cc-4b17-a661-39305b5b9533
-- title:
--   `BookProof.WeylHamiltonian.smul_nonneg_isPositive` (T : H →L[ℂ] H) (h : T.IsPositive) {c : ℝ} (hc : 0 ≤ c) : ((c : ℂ) • T).IsPositive
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylHamiltonian`.
--
--   `BookProof.WeylHamiltonian.smul_nonneg_isPositive` (T : H →L[ℂ] H) (h : T.IsPositive) {c : ℝ} (hc : 0 ≤ c) : ((c : ℂ) • T).IsPositive
--
--   Formalization note: Lean 4 identifier `BookProof.WeylHamiltonian.smul_nonneg_isPositive`.

-- Generated from ChapterWeylHamiltonian.lean — theorem BookProof.WeylHamiltonian.smul_nonneg_isPositive
import Mathlib
import Definitions.Def_ChapterWeylHamiltonian
open BookProof.WeylHamiltonian



open ContinuousLinearMap
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.WeylHamiltonian.smul_nonneg_isPositive (T : H →L[ℂ] H) (h : T.IsPositive)
    {c : ℝ} (hc : 0 ≤ c) : ((c : ℂ) • T).IsPositive := by sorry
