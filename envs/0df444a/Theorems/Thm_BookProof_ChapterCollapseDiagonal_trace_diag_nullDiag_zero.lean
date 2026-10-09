-- Prove2me | Theorems.Thm_BookProof_ChapterCollapseDiagonal_trace_diag_nullDiag_zero
-- name    : BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:14:57.873206+00:00
-- url     : https://prove2.me/theorems/d7a07e1b-21ad-4dd2-85ef-816018edbe27
-- title:
--   `BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero` (ρ O : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) (hO : ∀ i, O i i = 0) : (ρ * O).trace = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCollapseDiagonal`.
--
--   `BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero` (ρ O : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) (hO : ∀ i, O i i = 0) : (ρ * O).trace = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero`.

-- Generated from ChapterCollapseDiagonal.lean — theorem BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero
import Mathlib
import Definitions.Def_ChapterCollapseDiagonal
open BookProof.ChapterCollapseDiagonal


open scoped BigOperators
open Matrix


variable {n : ℕ}

theorem BookProof.ChapterCollapseDiagonal.trace_diag_nullDiag_zero (ρ O : Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsDiagonal ρ) (hO : ∀ i, O i i = 0) :
    (ρ * O).trace = 0 := by sorry
