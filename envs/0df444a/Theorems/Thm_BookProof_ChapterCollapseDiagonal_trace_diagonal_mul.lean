-- Prove2me | Theorems.Thm_BookProof_ChapterCollapseDiagonal_trace_diagonal_mul
-- name    : BookProof.ChapterCollapseDiagonal.trace_diagonal_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:14:35.18184+00:00
-- url     : https://prove2.me/theorems/0aab57f6-af63-4bb0-93cc-fb95c9222c10
-- title:
--   `BookProof.ChapterCollapseDiagonal.trace_diagonal_mul` (ρ O : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) : (ρ * O).trace = ∑ i, ρ i i * O i i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCollapseDiagonal`.
--
--   `BookProof.ChapterCollapseDiagonal.trace_diagonal_mul` (ρ O : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) : (ρ * O).trace = ∑ i, ρ i i * O i i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCollapseDiagonal.trace_diagonal_mul`.

-- Generated from ChapterCollapseDiagonal.lean — theorem BookProof.ChapterCollapseDiagonal.trace_diagonal_mul
import Mathlib
import Definitions.Def_ChapterCollapseDiagonal
open BookProof.ChapterCollapseDiagonal


open scoped BigOperators
open Matrix


variable {n : ℕ}

theorem BookProof.ChapterCollapseDiagonal.trace_diagonal_mul (ρ O : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) :
    (ρ * O).trace = ∑ i, ρ i i * O i i := by sorry
