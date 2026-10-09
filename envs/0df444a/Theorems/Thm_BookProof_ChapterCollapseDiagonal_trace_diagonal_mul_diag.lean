-- Prove2me | Theorems.Thm_BookProof_ChapterCollapseDiagonal_trace_diagonal_mul_diag
-- name    : BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:14:47.473517+00:00
-- url     : https://prove2.me/theorems/2c7fb83c-cd9f-4512-8f3a-d91d17cb5c01
-- title:
--   `BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag` (ρ D : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) : (ρ * D).trace = ∑ i, ρ i i * D i i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCollapseDiagonal`.
--
--   `BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag` (ρ D : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) : (ρ * D).trace = ∑ i, ρ i i * D i i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag`.

-- Generated from ChapterCollapseDiagonal.lean — theorem BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag
import Mathlib
import Definitions.Def_ChapterCollapseDiagonal
open BookProof.ChapterCollapseDiagonal


open scoped BigOperators
open Matrix


variable {n : ℕ}

theorem BookProof.ChapterCollapseDiagonal.trace_diagonal_mul_diag (ρ D : Matrix (Fin n) (Fin n) ℂ) (hρ : IsDiagonal ρ) :
    (ρ * D).trace = ∑ i, ρ i i * D i i := by sorry
